"""Azure review routing, credential isolation, failures, and quota reporting."""

import json
import subprocess
from types import SimpleNamespace

import pytest

from lean_pool import codex_review, review


def _request():
    return {
        "model": "gpt-6-astra",
        "effort": "xhigh",
        "messages": [
            {"role": "system", "content": "Review the contribution."},
            {"role": "user", "content": "Contributor text; $(do-not-execute)"},
        ],
    }


def test_default_routes_over_ssh_without_instantiating_openai(monkeypatch):
    """Even an ambient personal API key cannot divert the default backend."""
    monkeypatch.delenv("REVIEW_BACKEND", raising=False)
    monkeypatch.setenv("OPENAI_API_KEY", "must-not-be-used")
    monkeypatch.setenv("REVIEW_SSH_HOST", "review-azure")

    def no_openai(**kwargs):
        pytest.fail("The default backend must never instantiate the paid API client")

    def ssh(command, **kwargs):
        assert command[0] == "ssh"
        assert "StrictHostKeyChecking=yes" in command
        assert command[-2:] == ["review-azure", "lean-pool-review"]
        request = json.loads(kwargs["input"])
        assert request["model"] == "gpt-6-astra"
        assert request["effort"] == "xhigh"
        assert "Trust boundary" in request["messages"][0]["content"]
        assert "$(do-not-execute)" in request["messages"][1]["content"]
        assert "must-not-be-used" not in kwargs["input"]
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps(
                {
                    "model": "gpt-6-astra",
                    "effort": "xhigh",
                    "payload": {"summary": "ok", "verdict": "approve"},
                    "usage": {"prompt_tokens": 20, "completion_tokens": 10},
                }
            ),
        )

    monkeypatch.setattr(review, "OpenAI", no_openai)
    monkeypatch.setattr(codex_review.subprocess, "run", ssh)
    result = review.request_review(
        review.DEFAULT_MODEL, "rules", "$(do-not-execute)", "Review.", "xhigh"
    )
    assert result.payload["verdict"] == "approve"
    assert result.tier == "codex-azure"
    assert result.usage.prompt_tokens == 20
    footer = review.render_usage(result.usage, result.model, result.tier, result.effort)
    assert "no API credits" in footer
    assert "$" not in footer


@pytest.mark.parametrize(
    "failure", ["disconnect", "timeout", "bad-json", "wrong-model"]
)
def test_azure_failure_never_falls_back(monkeypatch, failure):
    """Transport and model failures stay failures even with API credentials."""
    monkeypatch.delenv("REVIEW_BACKEND", raising=False)
    monkeypatch.setenv("REVIEW_SSH_HOST", "review-azure")
    monkeypatch.setenv("OPENAI_API_KEY", "must-not-be-used")

    def no_openai(**kwargs):
        pytest.fail("API fallback is forbidden")

    def fail(*args, **kwargs):
        if failure == "timeout":
            raise subprocess.TimeoutExpired("ssh", 1)
        if failure == "disconnect":
            return SimpleNamespace(returncode=255, stderr="unreachable")
        stdout = "invalid" if failure == "bad-json" else '{"model": "other"}'
        return SimpleNamespace(returncode=0, stdout=stdout)

    monkeypatch.setattr(review, "OpenAI", no_openai)
    monkeypatch.setattr(codex_review.subprocess, "run", fail)
    with pytest.raises((RuntimeError, ValueError, subprocess.TimeoutExpired)):
        review.request_review(review.DEFAULT_MODEL, "rules", "diff", "Review.")


def test_unknown_backend_is_rejected(monkeypatch):
    """A configuration typo must not choose a billable backend."""
    monkeypatch.setenv("REVIEW_BACKEND", "codex-azur")
    with pytest.raises(ValueError, match="Unknown REVIEW_BACKEND"):
        review.request_review(review.DEFAULT_MODEL, "rules", "diff", "Review.")


@pytest.mark.parametrize(
    "field,value",
    [
        ("model", "gpt-5.6"),
        ("effort", "xhigh; echo unsafe"),
        ("messages", [{"role": "user", "content": "only one"}]),
    ],
)
def test_worker_rejects_invalid_requests(field, value):
    """The SSH endpoint cannot select a different model or execute commands."""
    request = _request()
    request[field] = value
    with pytest.raises(ValueError):
        codex_review.validate_request(request)


def test_worker_isolates_credentials_and_returns_structured_review(
    monkeypatch, tmp_path
):
    """Only ChatGPT authentication and text input reach the isolated process."""
    monkeypatch.setenv("OPENAI_API_KEY", "must-not-be-used")
    monkeypatch.setenv("GH_TOKEN", "must-not-be-forwarded")

    class Process:
        returncode = 0

        def communicate(self, text, timeout):
            assert text == _request()["messages"][1]["content"]
            (tmp_path / "answer.json").write_text(
                json.dumps(
                    {"review_json": json.dumps({"summary": "ok", "verdict": "approve"})}
                )
            )
            return (
                'dispatcher status\n{"type":"turn.completed",'
                '"usage":{"input_tokens":30,"output_tokens":15}}',
                "",
            )

    def spawn(command, **kwargs):
        assert command[0] == codex_review.CODEX
        assert 'forced_login_method="chatgpt"' in command
        assert "--ignore-user-config" in command
        assert "--ephemeral" in command
        assert command[command.index("--sandbox") + 1] == "read-only"
        assert "OPENAI_API_KEY" not in kwargs["env"]
        assert "GH_TOKEN" not in kwargs["env"]
        assert kwargs["start_new_session"]
        assert command[-1] == "-"
        assert _request()["messages"][1]["content"] not in command
        disabled = {
            command[i + 1] for i, flag in enumerate(command) if flag == "--disable"
        }
        assert {"shell_tool", "apps", "plugins", "multi_agent"} <= disabled
        return Process()

    monkeypatch.setattr(codex_review.subprocess, "Popen", spawn)
    response = codex_review.run_codex(_request(), tmp_path)
    assert response["payload"]["verdict"] == "approve"
    assert response["model"] == "gpt-6-astra"
    assert response["usage"] == {"prompt_tokens": 30, "completion_tokens": 15}


def test_worker_timeout_kills_process_group(monkeypatch, tmp_path):
    """Timeouts also stop the dispatcher and its model subprocesses."""
    killed = []

    class Process:
        pid = 1234
        calls = 0

        def communicate(self, *args, **kwargs):
            self.calls += 1
            if self.calls == 1:
                raise subprocess.TimeoutExpired("codex", 1)
            return "", ""

    monkeypatch.setattr(codex_review.subprocess, "Popen", lambda *a, **k: Process())
    monkeypatch.setattr(codex_review.os, "killpg", lambda *args: killed.append(args))
    with pytest.raises(RuntimeError, match="timed out"):
        codex_review.run_codex(_request(), tmp_path)
    assert killed == [(1234, codex_review.signal.SIGTERM)]


def test_azure_rubric_footer_reports_quota():
    """Five-rubric reviews report quota billing without inventing a dollar cost."""
    result = review.ReviewResult(
        {},
        SimpleNamespace(prompt_tokens=20, completion_tokens=10),
        codex_review.TIER,
        None,
        codex_review.MODEL,
        "xhigh",
    )
    outcomes = [SimpleNamespace(result=result)] * 5
    footer = review._render_rubric_usage(outcomes, "xhigh")
    assert "100 in / 50 out" in footer
    assert "no API credits" in footer
    assert "$" not in footer

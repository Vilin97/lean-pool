"""Review transport to the Azure VM's authenticated Codex account pool.

The SSH key is restricted to ``python3 worker.py --worker`` on the VM.
Only review text crosses SSH; neither GitHub nor OpenAI credentials do.
This module is also the standalone, standard-library-only remote worker.
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace
from typing import Any

MODEL = "gpt-6-astra"
TIER = "codex-azure"
TIMEOUT_SECONDS = 6000
MAX_REQUEST_BYTES = 4_000_000
WORKER_ROOT = Path("/data/lean-pool-review/jobs")
CODEX = "/home/vasil/.local/bin/codex-auto"


def request_completion(
    model: str, messages: list[dict[str, str]], effort: str | None
) -> tuple[Any, str, str | None]:
    """Call the forced-command SSH worker, with no API fallback."""
    host = os.environ.get("REVIEW_SSH_HOST")
    if not host or host.startswith("-"):
        raise RuntimeError("REVIEW_SSH_HOST must name the configured Azure SSH host")
    request = json.dumps({"model": model, "messages": messages, "effort": effort})
    configuration = os.environ.get("REVIEW_SSH_CONFIG")
    options = ["-F", configuration] if configuration else []
    process = subprocess.run(
        [
            "ssh",
            *options,
            "-T",
            "-o",
            "BatchMode=yes",
            "-o",
            "StrictHostKeyChecking=yes",
            "-o",
            "ConnectTimeout=15",
            "-o",
            "ServerAliveInterval=30",
            "-o",
            "ServerAliveCountMax=3",
            host,
            "lean-pool-review",
        ],
        input=request,
        text=True,
        capture_output=True,
        timeout=TIMEOUT_SECONDS + 60,
        check=False,
    )
    if process.returncode:
        raise RuntimeError(f"Azure Codex review failed: {process.stderr[-2000:]}")
    result = json.loads(process.stdout)
    if result.get("model") != model or not isinstance(result.get("payload"), dict):
        raise RuntimeError("Azure Codex worker returned an invalid review response")
    usage = result.get("usage")
    response = SimpleNamespace(
        choices=[
            SimpleNamespace(
                message=SimpleNamespace(content=json.dumps(result["payload"]))
            )
        ],
        model=result["model"],
        usage=SimpleNamespace(**usage) if usage else None,
    )
    return response, TIER, result["effort"]


def validate_request(request: dict) -> None:
    """Accept only the pinned model and two text messages, never commands."""
    if request.get("model") != MODEL:
        raise ValueError(f"The Azure reviewer only serves {MODEL}")
    if request.get("effort") not in (None, "low", "medium", "high", "xhigh", "max"):
        raise ValueError("Unsupported reasoning effort")
    messages = request.get("messages")
    if not isinstance(messages, list) or len(messages) != 2:
        raise ValueError("Expected a system message and a user message")
    for message, role in zip(messages, ("system", "user"), strict=True):
        if message.get("role") != role or not isinstance(message.get("content"), str):
            raise ValueError("Expected a system message and a user message")


def codex_command(request: dict, directory: Path) -> list[str]:
    """Build a fixed Codex invocation with tools and API-key auth disabled."""
    command = [
        CODEX,
        "exec",
        "--ignore-user-config",
        "--ephemeral",
        "--skip-git-repo-check",
        "--cd",
        str(directory),
        "--sandbox",
        "read-only",
        "--model",
        MODEL,
        "--json",
        "--output-last-message",
        str(directory / "answer.json"),
        "--output-schema",
        str(directory / "schema.json"),
        "-c",
        'forced_login_method="chatgpt"',
        "-c",
        'web_search="disabled"',
        "-c",
        "project_doc_max_bytes=0",
        "-c",
        "features.skip_host_skill_discovery=true",
        "-c",
        "base_instructions="
        + json.dumps(
            request["messages"][0]["content"]
            + "\nYou are a text-only reviewer. Do not use tools. Return the complete "
            "requested review JSON encoded as the review_json string in the output."
        ),
    ]
    for feature in (
        "shell_tool",
        "unified_exec",
        "view_image",
        "apps",
        "plugins",
        "hooks",
        "multi_agent",
        "multi_agent_v2",
        "skill_search",
        "image_generation",
        "computer_use",
        "browser_use",
        "browser_use_external",
        "sleep_tool",
    ):
        command.extend(["--disable", feature])
    if request.get("effort"):
        command.extend(
            ["-c", "model_reasoning_effort=" + json.dumps(request["effort"])]
        )
    return [*command, "-"]


def run_codex(request: dict, directory: Path) -> dict:
    """Run one bounded review and kill its whole process group on timeout."""
    schema = {
        "type": "object",
        "properties": {"review_json": {"type": "string"}},
        "required": ["review_json"],
        "additionalProperties": False,
    }
    (directory / "schema.json").write_text(json.dumps(schema))
    environment = {
        key: value
        for key, value in os.environ.items()
        if key
        not in (
            "OPENAI_API_KEY",
            "OPENAI_BASE_URL",
            "OPENAI_ORG_ID",
            "OPENAI_PROJECT_ID",
            "GH_TOKEN",
            "GITHUB_TOKEN",
            "CODEX_HOME",
        )
    }
    process = subprocess.Popen(
        codex_command(request, directory),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=environment,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(
            request["messages"][1]["content"], timeout=TIMEOUT_SECONDS
        )
    except subprocess.TimeoutExpired:
        stop_codex(process)
        raise RuntimeError("Azure Codex review timed out") from None
    except BaseException:
        stop_codex(process)
        raise
    if process.returncode:
        raise RuntimeError(f"Codex exited {process.returncode}: {stderr[-2000:]}")
    envelope = json.loads((directory / "answer.json").read_text())
    payload = json.loads(envelope["review_json"])
    if not isinstance(payload, dict) or not payload:
        raise ValueError("Codex did not return a review object")
    usage = extract_usage(stdout)
    return {
        "payload": payload,
        "model": MODEL,
        "effort": request["effort"],
        "usage": usage,
    }


def stop_codex(process: subprocess.Popen) -> None:
    """Let the account dispatcher forward termination to its separate child group."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.communicate(timeout=15)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()


def interrupted(signum: int, frame: Any) -> None:
    """Unwind the active worker when SSH disconnects or the job is cancelled."""
    raise InterruptedError(f"Review interrupted by signal {signum}")


def extract_usage(stdout: str) -> dict | None:
    """Read token counts from the final successful Codex turn event."""
    usage = None
    for line in stdout.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue  # The account dispatcher also emits plain-text status.
        if event.get("type") == "turn.completed" and event.get("usage"):
            usage = {
                "prompt_tokens": event["usage"].get("input_tokens", 0),
                "completion_tokens": event["usage"].get("output_tokens", 0),
            }
    return usage


def main() -> int:
    """Serve one SSH request using an isolated temporary directory on /data."""
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGHUP, interrupted)
    try:
        raw = sys.stdin.buffer.read(MAX_REQUEST_BYTES + 1)
        if len(raw) > MAX_REQUEST_BYTES:
            raise ValueError("Review request exceeds the worker size limit")
        request = json.loads(raw)
        validate_request(request)
        with tempfile.TemporaryDirectory(prefix="review-", dir=WORKER_ROOT) as name:
            response = run_codex(request, Path(name))
        print(json.dumps(response))
        return 0
    except Exception as error:
        print(f"Azure Codex review failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    if sys.argv[1:] != ["--worker"]:
        sys.exit("This entry point requires --worker")
    sys.exit(main())

"""An explicit fake HTTP vLLM server, not a language model or tokenizer."""

from contextlib import contextmanager
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
from threading import Thread

from eval.pipeline.inference.config import QWEN_MODEL, QWEN_REVISION


@contextmanager
def fake_vllm(directory: Path):
    state = {
        "model":QWEN_MODEL, "root":str(directory/"model"),
        "version":"0.32.0", "context_limit":65536,
        "finish_reason":"stop", "content":None, "token_count":None,
        "calls":[], "get_calls":[], "http_error":False,
    }

    class Handler(BaseHTTPRequestHandler):
        def log_message(self,*args):
            pass

        def reply(self,value,code=200):
            data = json.dumps(value).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type","application/json")
            self.send_header("Content-Length",str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            state["get_calls"].append(self.path)
            if self.path=="/v1/models":
                self.reply({"data":[{"id":state["model"],"root":state["root"]}]})
            elif self.path=="/version":
                self.reply({"version":state["version"]})
            else:
                self.reply({},404)

        def do_POST(self):
            payload = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
            state["calls"].append((self.path,payload))
            if self.path=="/tokenize":
                count = state["token_count"]
                if count is None:
                    # Deliberately fake; tests do not establish real context fit.
                    count = 10+sum(len(item["content"])//4 for item in payload["messages"])
                self.reply({"count":count,"max_model_len":state["context_limit"]})
            elif self.path=="/v1/chat/completions":
                if state["http_error"]:
                    self.reply({"error":{"message":"DO_NOT_PERSIST_RAW_ERROR_OR_PROMPT"}},400)
                    return
                system = payload["messages"][0]["content"]
                content = state["content"]
                if content is None:
                    if "standalone sledgehammer" in system:
                        content = "proof -\n  show ?thesis\n    sledgehammer\nqed"
                    elif "Isabelle/HOL proof engineer" in system:
                        content = "by simp"
                    else:
                        content = "### Step 1\nUse the source argument."
                self.reply({
                    "id":"fake-completion","model":state["model"],
                    "choices":[{"finish_reason":state["finish_reason"],
                                "message":{"role":"assistant","content":content,
                                           "reasoning":"HIDDEN_REASONING_MARKER",
                                           "reasoning_content":"HIDDEN_REASONING_MARKER"}}],
                    "usage":{"prompt_tokens":42,"completion_tokens":24,"total_tokens":66,
                             "completion_tokens_details":{"reasoning_tokens":8}},
                })
            else:
                self.reply({},404)

    server = ThreadingHTTPServer(("127.0.0.1",0),Handler)
    server.daemon_threads = True
    base = f"http://127.0.0.1:{server.server_port}/v1"
    manifest = {
        "schema_version":"itpeval_qwen_server_v1","model":QWEN_MODEL,
        "model_revision":QWEN_REVISION,"tokenizer_revision":QWEN_REVISION,
        "model_path":state["root"],"tokenizer_sha256":"a"*64,
        "template_sha256":"b"*64,"versions":{"vllm":"0.32.0"},
        "settings":{"max_model_len":65536,"dtype":"bfloat16","quantization":None},
        "base_url":base,"gpu":[{"name":"FAKE GPU"}],
    }
    manifest_path = directory/"server.json"
    manifest_path.write_text(json.dumps(manifest),encoding="utf-8")
    profile = {
        "backend":"vllm","model":QWEN_MODEL,"base_url":base,
        "model_revision":QWEN_REVISION,"tokenizer_revision":QWEN_REVISION,
        "server_manifest":str(manifest_path),"enable_thinking":True,
        "reasoning_effort":"medium","max_output_tokens":128,
        "temperature":1.0,"top_p":0.95,"top_k":20,"timeout_s":5,
    }
    profile_path = directory/"qwen.json"
    profile_path.write_text(json.dumps(profile),encoding="utf-8")
    state.update(profile=profile,profile_path=profile_path,manifest=manifest,manifest_path=manifest_path)
    thread = Thread(target=server.serve_forever,daemon=True)
    thread.start()
    try:
        yield state
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)

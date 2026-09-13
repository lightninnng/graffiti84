import json
import re
import subprocess
import sys


def token() -> str:
    out = subprocess.run(
        ["git", "-c", "credential.interactive=false", "credential", "fill"],
        input="protocol=https\nhost=github.com\n\n",
        capture_output=True, text=True,
    ).stdout
    return next(l.split("=", 1)[1] for l in out.splitlines() if l.startswith("password="))


tok = token()
hdr = ["-H", f"Authorization: Bearer {tok}"]
run_id = sys.argv[1] if len(sys.argv) > 1 else "34735918125"
url = f"https://api.github.com/repos/lightninnng/graffiti84/actions/runs/{run_id}/jobs"
jobs = json.loads(subprocess.run(["curl", "-s", *hdr, url], capture_output=True, text=True).stdout)
for job in jobs.get("jobs", []):
    print(f"job {job['id']} {job['name']}: {job['conclusion']}")
    for step in job["steps"]:
        print(f"  step {step['number']:>2} {step['name']}: {step['conclusion']}")
    log_url = f"https://api.github.com/repos/lightninnng/graffiti84/actions/jobs/{job['id']}/logs"
    log = subprocess.run(["curl", "-sL", *hdr, log_url], capture_output=True, text=True).stdout
    hits = [l for l in log.splitlines()
            if re.search(r"##\[error\]|error:|Error:|failed|Failed", l)]
    print("  --- error lines ---")
    for h in hits[:25]:
        print("  " + h[:300])

#!/usr/bin/env python3
"""
Generates kokoro config files based on template.
"""

ci_config = """\
# Format: //devtools/kokoro/config/proto/build.proto
# Generated from .github/kokoro/kokoro-cfg.py
# To regenerate run:
# cd .github/kokoro/ && python3 kokoro-cfg.py
build_file: "Surelog-%(kokoro_type)s-%(ci)s/.github/kokoro/%(ci)s.sh"
timeout_mins: 4320
env_vars {
  key: "KOKORO_TYPE"
  value: "%(kokoro_type)s"
}
env_vars {
  key: "KOKORO_DIR"
  value: "Surelog-%(kokoro_type)s-%(ci)s"
}
env_vars {
  key: "CI"
  value: "%(ci)s"
}
"""

for ci in ['test']:
    with open("continuous-%s.cfg" % ci, "w") as f:
        f.write(ci_config % {
            'ci': ci,
            'kokoro_type': 'continuous',
        })

    with open("presubmit-%s.cfg" % ci, "w") as f:
        f.write(ci_config % {
            'ci': ci,
            'kokoro_type': 'presubmit',
        })

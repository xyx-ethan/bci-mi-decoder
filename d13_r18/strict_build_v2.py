"""Strict acceptance wrapper: no mathematical theorem changes from strict_build.py."""
import strict_build as s

COPYRIGHT = r'''/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
'''

s.CORE = COPYRIGHT + s.CORE
for old, new in [
    ("example : OeisA67599.a 0 = 0 := by decide", "example : OeisA67599.a 0 = 0 := by decide +kernel"),
    ("example : OeisA67599.a 1 = 0 := by decide", "example : OeisA67599.a 1 = 0 := by decide +kernel"),
    ("example : OeisA67599.a 2 = 21 := by decide", "example : OeisA67599.a 2 = 21 := by decide +kernel"),
    ("example : OeisA67599.a 15 = 3151 := by decide", "example : OeisA67599.a 15 = 3151 := by decide +kernel"),
    ("example : OeisA67599.a 24 = 2331 := by decide", "example : OeisA67599.a 24 = 2331 := by decide +kernel"),
    ("example : OeisA67599.a 15 ≠ 3511 := by decide", "example : OeisA67599.a 15 ≠ 3511 := by decide +kernel"),
]:
    assert old in s.CORE, old
    s.CORE = s.CORE.replace(old, new, 1)

# Preserve the exact generator actually executed in the uploaded evidence.
_original_main = s.main
def audited_main():
    s.OUT.mkdir(parents=True, exist_ok=True)
    (s.OUT / "strict_build_v2.py").write_text(open(__file__, encoding="utf-8").read())
    _original_main()
s.main = audited_main

if __name__ == "__main__":
    try:
        s.main()
    except Exception as exc:
        s.status["error"] = repr(exc)
        s.save()
        raise

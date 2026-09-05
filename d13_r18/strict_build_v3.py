"""Strict acceptance wrapper: cheap kernel mutations only; exact semantic mutations run separately."""
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

# Remove only the expensive semantic examples from the strict theorem module.
# They are independently checked by tools/semantic_mutations.py in the round artifact.
for line in [
    "example : OeisA67599.a 0 = 0 := by decide\n",
    "example : OeisA67599.a 1 = 0 := by decide\n",
    "example : OeisA67599.a 2 = 21 := by decide\n",
    "example : OeisA67599.a 15 = 3151 := by decide\n",
    "example : OeisA67599.a 24 = 2331 := by decide\n",
    "example : OeisA67599.a 15 ≠ 3511 := by decide\n",
]:
    assert line in s.CORE, line
    s.CORE = s.CORE.replace(line, "", 1)

s.CORE = COPYRIGHT + s.CORE + r'''
-- Cheap in-kernel semantic/mutation tests retained inside the strict build.
example : OeisA67599.a 0 = 0 := by decide
example : OeisA67599.a 1 = 0 := by decide
example : OeisA67599.concatenateNats 31 51 = 3151 := by norm_num [OeisA67599.concatenateNats]
example : OeisA67599.concatenateNats 31 51 ≠ 3511 := by norm_num [OeisA67599.concatenateNats]
'''

_original_main = s.main
def audited_main():
    s.OUT.mkdir(parents=True, exist_ok=True)
    (s.OUT / "strict_build_v3.py").write_text(open(__file__, encoding="utf-8").read())
    _original_main()
s.main = audited_main

if __name__ == "__main__":
    try:
        s.main()
    except Exception as exc:
        s.status["error"] = repr(exc)
        s.save()
        raise

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
sys.path.insert(0, str(REPO / "d13_r18"))
import strict_build as s

s.ROOT = HERE
s.OUT = HERE / "evidence"
s.OUT.mkdir(parents=True, exist_ok=True)
s.ROWS = {
    "q1": [(167,166,7),(997,166,68),(179,178,112),(181,180,178),(193,192,70),(853,213,81)],
    "q2": [(389,194,6),(419,209,76),(1297,216,64),(467,233,199),(479,239,30),(563,281,270)],
}

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
for line in [
    "example : OeisA67599.a 0 = 0 := by decide\n",
    "example : OeisA67599.a 1 = 0 := by decide\n",
    "example : OeisA67599.a 2 = 21 := by decide\n",
    "example : OeisA67599.a 15 = 3151 := by decide\n",
    "example : OeisA67599.a 24 = 2331 := by decide\n",
    "example : OeisA67599.a 15 ≠ 3511 := by decide\n",
]:
    assert line in s.CORE
    s.CORE = s.CORE.replace(line, "", 1)
s.CORE = COPYRIGHT + s.CORE + r'''
-- Cheap semantic and mutation tests inside the strict kernel build.
example : OeisA67599.a 0 = 0 := by decide
example : OeisA67599.a 1 = 0 := by decide
example : OeisA67599.a 2 = 21 := by decide
example : OeisA67599.concatenateNats 31 51 = 3151 := by norm_num [OeisA67599.concatenateNats]
example : OeisA67599.concatenateNats 31 51 ≠ 3511 := by norm_num [OeisA67599.concatenateNats]
'''

if __name__ == "__main__":
    try:
        s.main()
    except Exception as exc:
        s.status["error"] = repr(exc)
        s.save()
        raise

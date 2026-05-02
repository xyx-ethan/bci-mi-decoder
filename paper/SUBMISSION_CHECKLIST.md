# JOSS submission checklist for `bci-mi-decoder`

This file tracks the steps required to submit `bci-mi-decoder` to the
**Journal of Open Source Software** (JOSS, <https://joss.theoj.org>).

## 1. Pre-submission requirements (per JOSS guidelines)

| # | Requirement | Status |
|---|-------------|--------|
| 1 | Open-source license (OSI-approved) | ✅ MIT (`LICENSE`) |
| 2 | Repository hosted at a long-term archive (GitHub/GitLab/etc.) | ✅ <https://github.com/xyx-ethan/bci-mi-decoder> |
| 3 | "Substantial scholarly effort" — at least three months of work or significant novelty | ✅ Two-month challenge submission codepath; broader package evolved over a longer period |
| 4 | Functional, with automated tests | ✅ `pytest tests/` passes (6/6) |
| 5 | Documentation: usage examples, installation, API outline | ✅ `README.md`, `docs/methodology.md`, `docs/results.md` |
| 6 | Statement of need explained for non-experts | ✅ See `paper/paper.md` § Statement of need |
| 7 | Comparison to related software | ✅ `paper/paper.md` cites MOABB, Braindecode, MNE-Python, pyRiemann |
| 8 | Citation file at repo root | ✅ `CITATION.cff` |
| 9 | `paper/paper.md` (250–1000 words) | ✅ ~620 words |
| 10 | `paper/paper.bib` with all citations resolved | ✅ |
| 11 | Author ORCID(s) | ⚠️ Placeholder — register at <https://orcid.org> and replace `0000-0000-0000-0000` in `paper/paper.md` and `CITATION.cff` |
| 12 | A versioned, taggable release | ✅ `v0.1.0` Git tag and GitHub release |
| 13 | Persistent archive (Zenodo, Software Heritage, etc.) | ⏳ See § 3 |

## 2. Author ORCID registration

JOSS requires every listed author to have an ORCID iD. If you do not yet
have one:

1. Register a free ORCID at <https://orcid.org/register> (~5 min).
2. Replace the placeholder `0000-0000-0000-0000` in two files:
   - `paper/paper.md` (line: `    orcid: 0000-0000-0000-0000`)
   - `CITATION.cff` (line: `    orcid: "https://orcid.org/0000-0000-0000-0000"`)

## 3. Zenodo archive (recommended before submission)

JOSS asks reviewers to confirm that a permanent archive of the reviewed
software exists. The cleanest path is:

1. Sign in at <https://zenodo.org> with your GitHub account.
2. Open the **GitHub** tab and toggle the `xyx-ethan/bci-mi-decoder`
   repository to *On* in the Zenodo–GitHub integration.
3. On GitHub, draft a release for the existing `v0.1.0` tag (if not
   already a Release object); Zenodo will auto-mint a DOI.
4. Note the DOI (looks like `10.5281/zenodo.NNNNNNN`); JOSS will ask
   for it during the pre-review.

## 4. Submission process

1. Visit <https://joss.theoj.org/papers/new>.
2. Fill the form with:
   - Repository URL: `https://github.com/xyx-ethan/bci-mi-decoder`
   - Branch / commit / tag: `v0.1.0`
   - Path to paper: `paper/paper.md`
   - Software archive DOI: (Zenodo DOI from § 3)
3. Submit. JOSS opens a public pre-review issue on the
   `openjournals/joss-reviews` GitHub repository within 24–48 h.
4. The editor assigns reviewers; the review is conducted as a public
   GitHub issue. Typical decision time: **2–6 weeks**.

## 5. Local PDF preview (optional sanity check before submitting)

A GitHub Action (`.github/workflows/draft-pdf.yml`) automatically builds
the paper PDF on every push to `paper/**`. To preview locally:

```bash
docker run --rm \
  --volume $PWD/paper:/data \
  --user $(id -u):$(id -g) \
  --env JOURNAL=joss \
  openjournals/inara
```

The output appears at `paper/paper.pdf`.

## 6. Common JOSS desk-rejection triggers (sanity-check before submitting)

- [ ] Word count of body text inside 250–1000 (counting Summary +
      Statement of need + Functionality + Compliance + Acknowledgements,
      excluding YAML frontmatter and references).
- [ ] All references resolve (no broken DOIs).
- [ ] Software is genuinely open-source and the license file is in the
      repo (not just on the PyPI page).
- [ ] No claims of novelty that the paper itself is the publication —
      JOSS is for *software*, not for new research results.
- [ ] Repository is not just a personal experiment script collection.
- [ ] At least one functional test covering the main use case.
- [ ] No commercial / closed-source dependency required to use the
      software.

## 7. After acceptance

JOSS will:

- Mint a DOI for the JOSS paper (typically `10.21105/joss.NNNNN`).
- Provide a citation block to add to `README.md` and `CITATION.cff`.
- Add the paper to JOSS's Crossref-indexed catalogue, making it
  searchable on Google Scholar, Web of Science (via Crossref), and
  similar indices.

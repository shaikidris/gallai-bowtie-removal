# Palomar readiness tracker

Status: PREPARATION. Contract, Apache-2.0, and private GitHub checkpoint/push approved. Public publication is not approved.
Research theorem scope: eight of eight paper deliveries formally closed.
Release selected surface: six declarations, corresponding to A/B/C/A1/A2.

| Stage | Status | Remaining exit test |
|---|---|---|
| P1 source freeze/licence | DONE | Per-file source/release hashes saved; original files unchanged |
| P2 Challenge/Solution | IN PROGRESS | Challenge standalone build PASS; Solution typed in source environment; extracted build and Comparator identity pending |
| P3 extraction/build | IN PROGRESS | 973 modules copied; strict tracked cone audit PASS; standalone Solution build live |
| P4 independent verification | TODO | Exact exporter/dependency gate, Comparator, NanoDa |
| P5 metadata/rehearsal | TODO | Current schemas, assessability, current preflight/full replay |
| P6 public handoff | TODO | Exact immutable checked commit, explicit push approval, manual intake |

Approved limits:1000 local Lean modules,125000 lines,800 Challenge lines,
six selected theorems,zero source-import-unreachable release modules.
Current extracted proof modules973/119379 original lines; licence headers add
962 lines. Challenge269 lines; Solution is a six-theorem exact wrapper.
Recount after every interface change; these are import counts, not a claim of
kernel-minimal proof terms.

Local .lake/packages is an ignored dependency-cache link to the pinned source
cache. It is not part of the release, a proof-source dependency, or a clean
Linux replay. No external state has changed.

## Readiness iteration R1 — 2026-09-13

- Source extraction passed with hashes for all973 modules and header-only
  Apache licence conversion; original proof files untouched.
- Standalone `lake build Challenge` session69160 exit0/1192jobs, Challenge14s;
  exactly six deliberate theorem holes, no extra helper holes.
- `Solution.lean` checked in the research environment (session49647's second
  command exited0); this is preliminary, not extracted-build evidence.
- Extracted `lake build Solution` is running in session48962; output at
  `/tmp/gallai-release-solution.log`. Re-poll this handle, do not restart merely
  because output is quiet. It rebuilds licensed source modules, not proofs
  imported from the source laboratory.
- Strict source-cone audit exit0:975 local modules/120696lines;
  Challenge1module/269lines;Solution974modules/120427lines;unreachable0.
  Licence,6/6 theorem docstrings and nine package pins passed. Warnings:
  uncommitted snapshot and final source-commit/provenance reconciliation.
- Exact exporter gate PASS: Lean4.33.0; exporter15f6055e299ad5b89345e533cc2192f4cc00f659.
- Trusted dependency provenance PASS: Mathlibdb584cd6d46c92f209a44c0f1c829460d327499d
  is an ancestor of the canonical master branch. Both gates used public
  Palomar policyef2fa1eadcb246c2346ddba39b52eaa53d4bb763.
- Current Palomar `load_formalization_metadata` validation PASS with PyYAML6.0.3.
  This is the metadata minimum only, not complete prepare/full verification.
- Linux replay environment unavailable: colima reports missing Lima; no Docker,
  Podman or Orb command found. No VM software was installed or started.
- No commit, remote, push or live submission. The package is NOT READY yet.

Remaining named obligations: standalone Solution build; Comparator and NanoDa;
complete current prepare/full replay; final independent statement/readability
review; immutable source/release checkpoint and authorized public handoff.

## Private checkpoint and cross-record preparation — 2026-09-13

The private release repository is `shaikidris/gallai-bowtie-removal`, verified
PRIVATE through GitHub. This checkpoint is not a completed verification release.
The live build remains the R1 process; no restart was requested.
Zenodo software, SSRN preprint, and Palomar metadata are being prepared locally.
No DOI, SSRN identifier, or Palomar registration exists in this preparation.
See `SUBMISSION_LINKS.md` for the reciprocal-link sequence. Private GitHub
availability does not satisfy Palomar's public immutable-source requirement.

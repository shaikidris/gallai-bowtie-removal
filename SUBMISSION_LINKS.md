# Publication links — preparation only

The source repository is private: https://github.com/shaikidris/gallai-bowtie-removal.
Do not use it as an accessible referee artifact until public access is approved.

Three distinct records are planned:

| Record | Object | Identifier/status |
|---|---|---|
| Zenodo | Apache-2.0 Lean software source archive at an immutable release | Not reserved or published |
| SSRN | Manuscript *Gallai’s Path Decomposition Conjecture for Graphs with Small Bowtie Boundaries* | User reports submitted on 2026-09-13; identifier and public landing page pending |
| Palomar | Six declarations selected in comparator.json | Independent verification and registration pending |

After an SSRN landing page exists, replace the unpublished-source location in
formalization.yaml with its actual stable identifier, preserving the manuscript
version and provenance digest. This is the Palomar-to-SSRN reference.
After Palomar registration, cite its actual entry/version and verified source
commit in the SSRN manuscript's formalization section. Until then, describe it
only as planned verification, not an accepted or registered result.

For Zenodo, the software record should be `isSupplementTo` the actual SSRN
paper identifier. Cite the software DOI in the paper. Link Palomar as a separate
verification record once it exists; it does not replace the software or paper.
Reserve a software DOI only through an approved deposit, never invent one.

Gate order: finish extracted build and independent checks; approve public source
access; approve paper freeze and inspect the resulting PDF; approve deposits;
record real identifiers; synchronize metadata and make a new immutable checkpoint
where necessary; hand Palomar intake to the user. No circular prerequisite is
needed: the paper can initially state that Palomar verification is pending.

Local preparation packet: ../submission-preparation/README.md.
No manuscript PDF was generated for this checkpoint.

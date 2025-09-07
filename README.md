# Wild_LIFE — SWHAP Workbench

This repository contains the curated acquisition of the **Wild_LIFE / LIFE system**
developed at the DEC Paris Research Lab, following the [Software Heritage Acquisition Process (SWHAP)](https://github.com/SoftwareHeritage/swhapguide).

The workbench provides both the *Depository* and the *Curated Source Code Deposit*:

- [`raw_materials/`](./raw_materials)  
  Contains the pristine release tarballs (`life_090.tgz`, `life_091.tgz`, `life_10.tgz`) and ancillary material (README, license).

- [`metadata/`](./metadata)  
  Contains all curatorial metadata:  
  - `catalogue.md` — project-level description  
  - `version_history.csv` — version table with checksums and dates  
  - `journal.md` — provenance log of curation actions  
  - `codemeta.json` — machine-readable metadata  
  - `license.txt`, `readme.txt`, `checksums.sha256`, etc.

- [Curated Source Code Deposit](../../tree/SourceCode) (branch `SourceCode`)  
  A reconstructed Git history with one commit per release (0.90, 0.91, 1.0), annotated tags, and sources flattened at the root.  
  Empty directories from the original archives are preserved using `.emptydir` markers.

---

## How to use this workbench

- To inspect the *original materials*, browse the [`raw_materials/`](./raw_materials) and [`metadata/`](./metadata) directories on this branch.  
- To inspect the *reconstructed source code history*, switch to the [`SourceCode` branch](../../tree/SourceCode).  
- For full methodological details, see the [SWHAP Guide](https://github.com/SoftwareHeritage/swhapguide).

---

**Curator:** Roberto Di Cosmo <roberto@dicosmo.org>  
**Date:** 2025-09-07  

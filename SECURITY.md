# Security & privacy

This repository is **public**. Keep it free of secrets and personal machine paths.

1. Never commit `.env` files with secrets, API tokens, SSH keys, or personal absolute paths.
2. Prefer relative paths in docs (`lean/`, `reports/`, …).
3. Machine-local build logs that embed home directories are gitignored (`build_*.txt`, `lean/*.log`, …).
4. If a secret was ever committed, rotate it and rewrite history immediately.
5. The tracked `portable_cpu/profiles/high_ram.env` is a non-secret resource-tuning profile only (job counts / Lean threads).

Report security issues privately to the repository owner (do not open a public issue with secrets).

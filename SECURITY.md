# Security & privacy

This repository is intended to be published later. Before any public release:

1. Keep the GitHub repository **private** until an explicit public switch.
2. Never commit `.env`, API tokens, SSH keys, or personal absolute paths.
3. Prefer relative paths in docs (`lean/`, `reports/`, …).
4. Machine-local build logs that embed home directories are gitignored (`build_*.txt`, `lean/*.log`, …).
5. If a secret was ever committed, rotate it and rewrite history before going public.

Report security issues privately to the repository owner (do not open a public issue with secrets).

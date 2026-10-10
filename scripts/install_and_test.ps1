# Requires: Python 3.11+
python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -U pip
pip install -e ".[dev]"
pytest
Write-Host "OK — evidence policy remains: no P vs NP claims below E5."

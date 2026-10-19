web: gunicorn app:app --bind 0.0.0.0:${PORT:-8000} --worker-class gthread --workers 1 --threads 48 --timeout 300

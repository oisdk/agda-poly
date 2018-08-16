#!/usr/bin/env bash
find src -name "*.agdai" -type f -delete
echo "Typecheck examples"
time find src -name "Examples.agda" -exec agda {} \;

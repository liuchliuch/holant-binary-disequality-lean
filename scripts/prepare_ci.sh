#!/usr/bin/env bash
# Allocate resources only on disposable GitHub-hosted Linux runners.
set -euo pipefail
[[ "${GITHUB_ACTIONS:-}" == true && "${RUNNER_ENVIRONMENT:-}" == github-hosted ]]
[[ "$(uname -s)" == Linux ]]
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /usr/local/.ghcup /opt/hostedtoolcache/CodeQL
sudo swapoff -a
sudo rm -f /swapfile /mnt/swapfile
swap_path="${RUNNER_TEMP}/holant-swap"
sudo fallocate -l 32G "$swap_path"
sudo chmod 600 "$swap_path"
sudo mkswap "$swap_path"
sudo swapon "$swap_path"
sudo apt-get update -qq
sudo apt-get install -y --no-install-recommends qpdf zstd
free -h
df -h .

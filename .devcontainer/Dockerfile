# coqorg/coq ships Debian bookworm + opam with Coq already built, plus the
# toolchain the opam packages below need (gcc/g++, m4, make, git, python3.11,
# sudo) and dune, which is what this project builds with. The opam switch is
# exported as Docker ENV, so coqc/dune/coq-lsp are on PATH in every shell
# without an `eval $(opam env)`.
#
# Only linux/amd64 images are published, so on Apple Silicon this builds and
# runs under emulation (correct, but slow).
#
# TensorRocq supports Rocq 8.20-9.1, but the Examples/ only build on 8.20 (see
# README, "Setup"), so 8.20 is the version that builds the whole repo. On 8.x
# the opam packages are still named coq-*, not rocq-*.
ARG COQ_VERSION=8.20
FROM --platform=linux/amd64 coqorg/coq:${COQ_VERSION}

USER coq
WORKDIR /home/coq

# The coq-released repo is already configured in this image, so the README's
# `opam repo add` step is a no-op here and is skipped.
#
# Pin SQIR/VOQC/VyZX with -n (no action) and install everything in one solver
# pass: coq-lsp forces a rebuild of coq itself, and doing it in one go avoids
# rebuilding QuantumLib/SQIR/VOQC/VyZX a second time on top of the new coq.
#
#   - coq-stdpp              README, "Installing TensorRocq": the one dependency
#                            of the library itself (`make` / `make tensors`)
#   - coq-quantumlib         README, "Building Examples"
#   - coq-sqir / coq-voqc    README, "Building Examples" (pinned to git)
#   - coq-vyzx               README, "Building Examples" (pinned to git);
#                            needed by Examples/VyZXExample.v
#   - coq-lsp                backs the VSCode extension in devcontainer.json
#
# TensorRocq itself is NOT installed here: the repo is mounted as the
# workspace and built in place with `make` / `make examples`, so the opam pin
# from the README would only shadow the working copy.
RUN opam update -y \
    && opam pin -y -n coq-sqir https://github.com/inQWIRE/SQIR.git \
    && opam pin -y -n coq-voqc https://github.com/inQWIRE/SQIR.git \
    && opam pin -y -n coq-vyzx https://github.com/inQWIRE/VyZX.git \
    && opam install -y coq-stdpp coq-quantumlib coq-sqir coq-voqc coq-vyzx coq-lsp \
    && opam clean -a -c -s --logs

# The editor's terminal forwards a locale (LC_ALL/LANG=en_US.UTF-8) that this
# image does not have generated -- it ships only C, C.utf8 and POSIX -- so every
# bash invocation prints
#   /bin/bash: warning: setlocale: LC_ALL: cannot change locale (en_US.UTF-8)
# Generating the locale silences it. Kept after the opam layer so it does not
# invalidate that (much more expensive) build step.
USER root
RUN apt-get update \
    && apt-get install -y --no-install-recommends locales \
    && sed -i 's/^# *\(en_US.UTF-8 UTF-8\)/\1/' /etc/locale.gen \
    && locale-gen \
    && rm -rf /var/lib/apt/lists/*
ENV LANG=en_US.UTF-8
USER coq

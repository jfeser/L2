#!/bin/bash

# Parameters:
OPAM_ROOT=/usr/local/opam

# Update system.
apt-get update
apt-get -y upgrade

# Install ocaml packages.
apt-get -y install ocaml-nox ocaml-native-compilers ocaml-findlib opam m4 gettext zlib1g-dev libcurl4-openssl-dev autoconf camlp4-extra

# Install opam and packages.
mkdir -p $OPAM_ROOT
opam init --auto-setup --yes --root $OPAM_ROOT
eval "$(opam config env --root $OPAM_ROOT)"
opam install -y core menhir utop bolt

# Set permissions so that the user can install using opam.
chown -R vagrant:vagrant $OPAM_ROOT
sudo -i -u vagrant opam init --auto-setup --yes --root $OPAM_ROOT

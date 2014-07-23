#!/bin/bash

# Parameters:
OPAM_ROOT=/usr/local/opam

# Update system.
apt-get update
apt-get -y upgrade

# Install ocaml packages.
apt-get -y install ocaml-nox ocaml-native-compilers opam m4 gettext zlib1g-dev libcurl4-openssl-dev autoconf

# Install opam and packages.
mkdir -p $OPAM_ROOT
opam init --auto-setup --yes --root $OPAM_ROOT
eval "$(opam config env --root $OPAM_ROOT)"
opam install -y core menhir utop

# Install updated git.
if [ "$(git --version)" == 'git version 1.9.1' ]; then
    cd /tmp
    git clone https://github.com/git/git.git
    cd git
    make configure
    ./configure --prefix=/usr
    make all
    make install
    cd /tmp
    rm -rf git
fi

# Install Z3 with OCaml bindings.
git clone https://git01.codeplex.com/z3
cd z3
git checkout ml-ng
python2 scripts/mk_make.py --ml
cd build
make
make install
cd /tmp
rm -rf z3

# Set permissions so that the user can install using opam.
chown -R vagrant:vagrant $OPAM_ROOT
sudo -u vagrant opam init --auto-setup --yes --root $OPAM_ROOT

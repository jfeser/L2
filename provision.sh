#!/bin/bash

# Update system.
sudo apt-get update
sudo apt-get -y upgrade

# Install ocaml packages.
sudo apt-get -y install ocaml-nox ocaml-native-compilers opam m4 gettext zlib1g-dev libcurl4-openssl-dev autoconf

# Install opam and packages.
OPAM_ROOT=/usr/local/opam
sudo mkdir -p $OPAM_ROOT
sudo chown vagrant:vagrant $OPAM_ROOT
opam init -y --root $OPAM_ROOT 
sudo opam init -y --root $OPAM_ROOT
eval `opam config env --root=/usr/local/opam`
opam install -y core menhir utop

# Install updated git.
if [ "$(git --version)" == 'git version 1.9.1' ]; then
    cd /tmp
    git clone https://github.com/git/git.git
    cd git
    make configure 
    ./configure --prefix=/usr
    make all
    sudo make install
    cd ..
    rm -r git
fi

# Install Z3 with OCaml bindings.
git clone https://git01.codeplex.com/z3
cd z3
git checkout ml-ng
python2 scripts/mk_make.py --ml
cd build
make
echo '#!/bin/bash' > install.sh 
echo 'eval `opam config --root /usr/local/opam env`' >> install.sh 
echo 'echo $PATH' >> install.sh 
echo 'make install; chown -R vagrant:vagrant /usr/local/opam' >> install.sh
chmod +x install.sh
sudo ./install.sh
cd ..
rm -r z3



#!/bin/sh
rm -f coq.kernel
ln -s $(find -L $(coqc --config | sed -n -E -e '/^COQLIB=/s;^COQLIB=(.*)/coq;\1/ocaml;p') -type d -name kernel) coq.kernel

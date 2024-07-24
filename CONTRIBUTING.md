# Contributing to Kôika

To start contributing, you need a GitHub account and create a pull-request against this repository.
See [here](https://docs.github.com/en/get-started/quickstart/hello-world) for a primer.

# How to do

## Before submitting a pull request

Run the tests to check if your changes broke anything.
You will do everyone the biggest favour if you run the continuous integration runner to build and test Kôika.
This assumes that you have the [Nix](https://nixos.org/download) Package Manager installed with the support for flakes enabled.
Suppose Nix is set up correctly, you just run:

```sh
nix run .#makes -- . /build
```

## Locally reproduce a CI run

Suppose you want to produce a CI run locally, maybe because it has failed on GitHub or because you want to run it on a different commit of a pull request that consist of multiple commits.
You can adapt the previously shown call to `makes` to do that; replace `<rev>` with the commit hash of interest:

```sh
# use the commit directly from GitHub
nix run .#makes -- github:Barkhausen-Institut/koika@<rev> /build
# alternatively, if the commit is already locally available
nix run .#makes -- local:"$PWD"@<rev> /build
```

If necessary, `makes` downloads the repository in the state given in `<rev>` and executes the CI script referenced via `/build`.

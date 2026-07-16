# mk-redex-rocq

miniKanren semantics formalized in Rocq.

## Building

**Dependencies:** Rocq (Coq), `coq_makefile`, and the Rocq standard library.

### With Nix

```sh
nix build
```

Or enter a development shell (also sets up `Makefile.coq`):

```sh
nix develop
```

### Without Nix

Ensure `coq` and `coq_makefile` are on your `PATH`, then:

```sh
make
```
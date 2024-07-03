# Dolmen_Skolemize

Dolmen_Skolemize parses the FOF formulas from a TPTP problem by skolemizing them using [**Dolmen**](<https://github.com/Gbury/dolmen/>).

## Installation

### DEPENDENCIES

This depends on:
- `OCaml`
- `Dolmen`

Check the installation of [`Dolmen`](<https://github.com/Gbury/dolmen/blob/master/README.md>).


### COMPILATION
In order to compile, use:

```bash
make
make install
```

You can try the parser:

```bash
./delmon_skolemize test/reflexif.p test/reflexif_dolmen.p
```

You can also delete `_buid` and the executable generated:

```bash
make clean
```
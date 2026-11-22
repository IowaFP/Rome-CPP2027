# Section 2: Rows in Action

Section 2 describes many Rosi types; [RowsInAction.ro](./RowsInAction.ro) is a
Rosi file that gives terms to each type using Rosi's highly expressive forms 
of label-generic programming.

## Background
I would recommend reading through parts of our unpublished manuscript on System Rωμ, 
[Abstracting Extensible Recursive Functions](https://arxiv.org/abs/2410.11742), to learn about Rosi's term structure.

## Installation and Usage
To run the code:

1. Download [Rosi](https://github.com/IowaFP/Rosi)
1. Install a Rosi executable with [Cabal](https://www.haskell.org/cabal/) to your $PATH:
   ```sh
   cabal install --installdir=/your/bin/path --overwrite-policy=always
   ```
1. (Optional) You may also install Rosi's VS Code support for syntax highlighting via [Rosi-VSCode](https://github.com/IowaFP/rosi-vscode). It is available via the Code Extensions store.
1. Run the `rosi` executable on [RowsInAction.ro](./RowsInAction.ro):
   ```sh
   rosi RowsInAction.ro
   ```

Note that many definitions in [Ro.Base](./Ro/Base.ro) are the target of 
elaboration of Rosi's syntactic sugar, so it is crucial that `Ro.Base` 
be included. It is imperative that you include the base library (and `Data.Nat`) included in this repository, as it differs from Rosi's native [Ro.Base](https://github.com/IowaFP/Rosi/blob/main/rolib/Ro/Base.ro) library.

## Differences

Some syntax in the paper differs from Rosi syntax here, as:
1. I use some pseudo-syntax for clarity in the text, such as:
  - I write "row Point = ..." rather than "type Point = ...", 
    just to emphasize that what's being introduced is a row.
  - I write a × b instead of Pair a b, and a × b × c instead of Triple a b c
  - I write ⊤ instead of Unit
2. I leave maps implicit here, e.g., Π (Functor z) instead of 
   Π (Functor $ z), as in the text.
3. Rosi has a *lot* of syntactic sugar for more ergonomic programming, 
   such as:
   - left-hand arguments; 
   - equi-recursive type construction; 
   - inferred types; and
   - implicit type quantification. 
   There is also a lot of sugar I am not using, such as ('Foo: bar)
   for variant construction, and ('Foo: a → M) for variant elimination.

   
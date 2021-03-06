Cd "statdb-cli/src/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import Refinement.ExtrProg.
Require Import Variables.ExtrVariables.

Extraction Language Haskell.

Require Import StatDb.StatDbCli.

Extract Inlined Constant PeanoNat.Nat.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".

Separate Extraction cli.

(* Force extraction of the [Helpers] library since the initial student
 * code does not use it, but the students may need to use it, and the
 * build file (statdb-cli.cabal) lists it as a dependency.
 *)
Recursive Extraction Library Helpers.

Cd "../../".

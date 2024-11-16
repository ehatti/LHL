# LHL

## Overview

LHL is the first sound and complete program logic for _compositional linearizability_, which is a generalization of atomic linearizability, set linearizability, and interval linearizability. This makes it complete for concurrent objects. LHL uses a compositional model for concurrent computation which enables us to use the compositionality features of compositional linearizability to link verified components together into large systems
with a high-level of abstraction for their subcomponents. As a showcase, we verify the elimination-backoff stack
implementation modularly by verifying all of its sub-components against their linearized specifications and
then linking them together using compositional linearizability.

## Examples

- `Examples/Exchanger.v`: One-cell set-linearizable exchanger. Specification may be found in `Examples/ExchangerSpec.v`
- `Examples/ElimArray.v`: An exchanger array object that allows an arbitrary number of exchangers to execute concurrently
- `Examples/EBStack.v`: The atomic elimination backoff stack. Specification may be found in `Examples/AtomicStackSpec.v`

## Setup Steps

Compiled with Coq version 8.18.0, OCaml version 5.2.0.

We are using make. To build the project:
```
coq_makefile -f _CoqProject -o Makefile
make
```

You will also need to install Paco to compile this project. Install like so:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-paco
```

## Usage

The program logic is defined in `Logic.v`. Import this along with `Program` and `ProgramRules.v` to get the typical control flow constructs along with their derived rules. Modules are of type `Impl` -- once you define a module, you may verify it with he toplevel program logic judgement `VerifyImpl`. After this, you may import `LogicFacts.v` and use `soundness` to derive a linearizability proof.

From here, you may verify modules and compose them together using the theorems in `LinFacts.v`. `obs_ref` gives you vertical composition, and `locality` gives you horizontal composition.
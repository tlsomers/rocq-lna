Require Import Fourier.

Tactic Notation "lra" := 
    try fourier ; try ring_simplify ; reflexivity.

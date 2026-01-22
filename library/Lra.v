Require Import Fourier.

Tactic Notation "lraold" := 
    try fourier ; try ring_simplify ; reflexivity.

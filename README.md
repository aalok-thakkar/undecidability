# PCP# undecidability
This project formalizes the proof that Post's Correspondence Problem (PCP) is undecidable. The proof follows the reduction chain:
Lu​ ≤ m​MPCP ≤ m​PCP

    Universal Language (Lu​): We assume the undecidability of the Halting Problem/Universal Language.

    Modified PCP (MPCP): We simulate the computation trace of a Turing Machine M on input w as a string matching problem.

    PCP: We use the symbol-padding technique to reduce the "forced-start" MPCP to the general PCP.

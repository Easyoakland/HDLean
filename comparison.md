# Comparison to other for-verification HDLs
- CAVA (https://github.com/project-oak/silveroak), part of Google Research?: Coq + Lava. Like Lava, you describe a circuit using primitives and build up the circuit object to get your circuit. To prove things there is also an interpreter definition which describes how to software simulate the circuit and which you can prove things on.
    - Looks they ran into the same issue of no MonadFix in a strict language. Your looping construct must insert the delay itself. (Also I'm not sure MonadFix is even logically sound).
    - Looks abandoned?
- Kami (https://github.com/mit-plv/kami) and Koika (https://github.com/mit-plv/koika): Both Bluespec-like new languages (written as coq dsl) which works with an atomic transactions model. I think Koika is newer. From koika's github: "Our largest example at the moment is a simple RISCV (RV32I) 4-stage pipelined core."
- VossII (https://github.com/TeamVoss/VossII): Looks like a set of tools to help prove/understand system verilog designed circuits. "visualize, simulate and debug hardware descriptions"

# Conclusion
Interestingly, no Clash-like language with in-built proofs even though that's (in my opinion) the nicest of the neo-hdls I know of (first-class constructs of the language can be used in the circuit's dynamic behavior).
So I'm making Hdlean.
Maybe Koika will be easier to prove correctness in, but I get the impression that direct control over hardware output is limited, while in Clash you can tell exactly what registers and logic will exist in the final design, and there's no magic compiler. Enables the "move logic out of the compiler and into the libraries" concept. CAVA might be like that but it looks more annoying to write in for the reasons CLASH proposed itself over LAVA, and also because of the extra layer you have to go through to prove things about the interpreter of the generated circuit.


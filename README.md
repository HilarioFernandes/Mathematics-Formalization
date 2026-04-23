# Natural Number Game & Type Theory Notes

Welcome to my repository for learning Lean 4 and Type Theory! This project contains my personal notes and formalized code as I work through the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) and explore the foundations of type theory.

The goal of this repository is to document my journey learning interactive theorem proving, moving from informal mathematical proofs to formal verification in Lean.

## Repository Structure

- **`NaturalNumberGame/`**: Contains the Lean source code (`.lean` files) with my solutions and formal proofs for the Natural Number Game levels.
- **`Informal TeX Notes/`**: Contains LaTeX source files (`main.tex`) and the compiled PDF with my informal mathematical notes, explaining the concepts, theorems, and proofs that complement the formal Lean code.

## Getting Started

### Prerequisites

To interact with the Lean code in this repository, you will need to have Lean 4 installed. The recommended way to install Lean is via `elan`, the Lean version manager. 

1. Install Lean and `elan` by following the instructions on the [Lean 4 Setup Guide](https://leanprover.github.io/lean4/doc/setup.html).
2. For the best experience, use an editor with Lean 4 support (such as VS Code with the `lean4` extension).

### Building the Project

Once Lean is installed, you can build the Lean project by running:

```bash
lake build
```

### Compiling the TeX Notes

To compile the LaTeX notes, navigate to the `Informal TeX Notes/` directory and use your preferred LaTeX compiler (e.g., `latexmk`, `pdflatex`):

```bash
cd "Informal TeX Notes"
latexmk -pdf main.tex
```

## About the Natural Number Game

The Natural Number Game is an interactive tutorial developed to teach the basics of the Lean theorem prover. It guides you through proving fundamental properties of natural numbers (like commutativity and associativity of addition and multiplication) starting from Peano's axioms.

Through this project, I'm documenting my progress and expanding on the concepts introduced in the game to build a stronger foundation in type theory.

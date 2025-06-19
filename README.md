# Formalizing x64 binary semantics in Isabelle/HOL

## TODO
- [x] move `nth` to `nth_error` 
- [ ] semantics validation: check the consistency between our semantic model and the real-world hardare
- [ ] encode proof: complete the encode-decode proof

# How to install
- [Isabelle/HOL 2024](https://isabelle.in.tum.de/) (please set your PATH with e.g. `/YOUR-PATH/Isabelle2024`)

- [Isabelle AFP](https://www.isa-afp.org/download/) (unzip the AFP to your PATH, e.g. `/YOUR-PATH/afp`)

_Make sure you have installed some basic libs, e.g. gcc, git_

```shell

# set PATH 
cd ~
vim. bashrc 
# export PATH=$PATH:/YOUR-PATH/Isabelle2024/bin:...
source .bashrc

# test isabelle/hol
isabelle version
# Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u .
# Add AFP to Isabelle

# go to this repo folder and open this project in jedit
cd /YOUR-PATH/this-repo

# if using WSL, firstly adding the following libs, then 
# do make, the proof checking requires about 30 min~
make
```
## Install on WSL
```shell
# Ubuntu 22.04.3 LTS (GNU/Linux 5.15.153.1-microsoft-standard-WSL2 x86_64)
sudo apt-get install libxi6 libxtst6 libxrender1 fontconfig
```

# Link to Paper
- Section 3: [Syntax](theory/x64Syntax.thy), [Semantics](theory/x64Semantics.thy)
- Section 4: [x64 Encoder](theory/x64Assembler.thy), [x64 Decoder](theory/x64Disassembler.thy)
- Section 5: [Lemma1 Encoder implies Decoder](theory/x64DecodeProof.thy) (done), [Lemma2 Decoder implies Encoder](theory/x64EncodeProof.thy) (WIP), [Theorem 1 Encoder-Decoder equivalence](theory/x64EquivalenceProof.thy).


# x64 Reference
As Solana rBPF has a x86_64 JIT compiler which involves of ISA instructions encoding formats, we refer to [x64 Manual](https://cdrdv2.intel.com/v1/dl/getContent/671200), and if you read the comment with `P123` in the isabelle/hol file, which means, the source text description could be found in the x64 Manual `Page 123`. Good Luck~



### Update

**June 19, 2025**: We have removed the `rdtsc` instruction, as it was only present in dead code.

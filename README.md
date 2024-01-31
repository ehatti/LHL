# LHL
 
 Steps I took to setup:

 ```
 opam init
 eval $(opam env)
 opam update
 opam switch create LHL 4.13.1
 opam pin add coq 8.18.0
```

For VsCoq:
```
opam install vscoq-language-server
```

Generating Coq Makefile:
```
coq_makefile -f _CoqProject -o Makefile
```

To Install Paco
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-paco
```
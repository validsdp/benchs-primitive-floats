# Benchmarks

## Version de Coq

* Obligatoire : 8.14.

* Image Coq standard avec OCaml 4.07 et le paquet coq-native.

* Coq-Interval 4.3.1.

## Benchs CoqInterval

- (flottants primitifs / flottants émulés avec prec opt / flottants émulés 53-bit)
  × (vm_compute / TODO native-compute)

- si grosse différence entre colonnes 2 et 3, faire une autre colonne avec 30 bit (ancienne précision par défaut)

## ValidSDP

- [x] Check ValidSDP compile avec Coq 8.14
- [ ] TODO rerun the ValidSDP benchmarks as is:
  https://github.com/validsdp/benchs-primitive-floats/tree/master/random_posdef_matrices/matrices#readme

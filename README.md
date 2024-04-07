## SCOL_PROJECT

Implementation of HOL-0 subset in scala. Based on holzero-0.6.3 using scala 3.

## Project design

After finishing current TO DO port all the remaining files with
no dependencies, or with dependencies already created.
When using build-in scala functions note that in code to keep
hol-0 API.

### TO DO

For 11.04.2024

- [ ] Port dltree.ml
- [x] Port lib.ml (haven't properly tested functions, especially I have doubts about union_ and unions_, but most of it should be OK)
- [ ] Port names.ml (half way done)
- [x] Port reader.ml  (ported full Reader, but haven't tested it properly. Should be OK)
- [ ] Port wrap.ml (Some functions that do not require further modules)
- [ ] Port type.ml
- [ ] Port term.ml
- [ ] Port utils 1, 2

For 18.04.2024:

- [ ] Port lexer.ml
- [ ] Port boolalg.ml and boolclass.ml
- [ ] Port equal.ml
- [ ] Port bool.ml
- [ ] Port eqcong.ml

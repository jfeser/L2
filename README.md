# λ² [![Build Status](https://travis-ci.org/jfeser/L2.svg?branch=master)](https://travis-ci.org/jfeser/L2)
λ² is a tool for synthesizing functional programs from input-output examples. [Documentation](http://jfeser.github.io/L2/)

There are two versions of λ²:
 - *PLDI:* This is a slightly improved version of the code that we benchmarked for the PLDI 2015 paper. **Use this if you want to reproduce our benchmarks.**
 - *Development:* This version has significantly diverged and no longer performs similarly. However, it has many more features and the code is cleaner. **Use this if you want to extend λ².**

## Building

1. Clone the repository:

``` shell
git clone git@github.com:jfeser/L2.git; cd L2
```

2. Check for missing dependencies. Install anything that is missing.

``` shell
jbuilder external-lib-deps --missing @install
```

### PLDI version

2. Check out the `pldi-modernize` branch.

``` shell
git checkout pldi-modernize
```

3. Build using JBuilder.

```shell
jbuilder build @install
```

4. Try λ² on a benchmark problem by running:

```shell
_build/default/src/l2.exe benchmarks/concat.json
```

You should see output like:

``` text
Solved concat in 39ms. Solutions:
(let concat (let a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) _) _)
```

### Development version

2. Build using JBuilder.

``` shell
jbuilder build @install
```

3. Try λ² on a benchmark problem by running:

```shell
_build/default/src/l2-cli/l2_cli.exe synth -l components/stdlib.ml -dd higher_order,input_ctx specs/largest_n.json
```

You should see output like:

``` text
                            .lkO0K0xc.
                          'kk;.  .;kWXc    Synthesizing..
                         .NN,       kMMo
                         'WMWx      kMMk   Hypotheses verified: 48458
                          ;dkc     lWMX,      Hypotheses saved: 0
         .:loc.                  .OMWx.
       .okcdWMN,               .oXOc.      Memoization table hit rate: 98.16
      .0o   kMM0             .xNk'    ';
      .'    lMMN.          .cOl.     .KO   Hashcons table equals calls: 1139934 (718173 t, 421761 f)
            ;MMM,         lXWOddddddx0Md   Hashcons table hash calls: 891626, hashcons calls: 891626
            oMMM:        ;kkkkkkkkkkkkk,   Hashcons table len: 73738, num entries: 69923
          .ONWMMl                          Hashcons bucket sum: 160341, min: 0, med: 3, max: 21
         'XO.0MMo
        ,Ko  OMMx                          Signatures: 2785 none, 25306 checked, 18420 dups, 0 fails
      .xNc   xMMO
     ;NK,    dMM0
   .dNd.     lMMX.   ..
  ;XMo       :MMM'  ,O.
 dWNl        .NMMOlxd.
lKO:          ;KMNx.
Runtime: 5.4s
Found solution:
fun b a -> take (reverse (sort (concat a))) b
```

## Running benchmarks

Benchmark problems are in the `bench/` directory.

## Questions?

Send email to feser@csail.mit.edu.

## Publications

Feser, J. K., Chaudhuri, S., & Dillig, I. (2015, June). [Synthesizing data structure transformations from input-output examples.](http://dl.acm.org/citation.cfm?id=2737977) In Proceedings of the 36th ACM SIGPLAN Conference on Programming Language Design and Implementation (pp. 229-239). ACM.

The previous catalog was too vague. This version is explicit and self-contained.

Conventions:

* **basic** = intended to be startable after NNG4-level Lean fluency and no serious prior mathematics.
* **well covered** = a course at this scope can be built from current mathlib without large topical holes.
* **needs extension** = a standard course at this scope would run into real missing or thin areas.

## Foundations

1. **Finite sets, finsets, multisets, lists, and finite sums/products** — **basic** — **well covered**.
   This course is the finite-object infrastructure course: `Fin`, `Fintype`, `Finset`, finite sets as subtypes, lists versus multisets, permutations of lists, finitely supported functions, finite products of finsets, matrices over finite index types, and the big-operator layer that turns finite objects into usable mathematics. It should also include binomial coefficients, factorials, finite sums/products, and the counting identities that underlie later combinatorics and linear algebra. It should **not** try to include graph theory, Ramsey theory, or additive combinatorics; those belong later. ([Lean Community][2])

2. **Sets, functions, relations, equivalences, subtypes, and countability** — **basic** — **well covered**.
   This is the language course for modern mathlib: sets as predicates, images/preimages, restriction to subsets, injective/surjective/bijective-on-a-set maps, relations as sets of pairs, bundled equivalences and partial equivalences, subtypes, countable sets, and encodable types. It is where you teach the difference between equality, equivalence, and isomorphism, and where you normalize working with `↥s`, `Set.MapsTo`, `Set.InjOn`, `Equiv`, and `Encodable`. ([Lean Community][3])

3. **Orders, lattices, complete lattices, closure operators, Galois connections, and filters** — **basic** — **well covered**.
   This course should cover preorders/partial orders/linear orders, suprema and infima, complete lattices, fixed points of monotone maps, closure operators, Galois connections and insertions, and filters as order-theoretic convergence objects. This is the real prerequisite for serious topology, domain-style reasoning, and a lot of category-theoretic examples; it is not just “order theory in the small.” ([Lean Community][4])

4. **Algebraic structures, homomorphisms, scalar actions, modules, and submodules** — **basic** — **well covered**.
   This is the algebra-hierarchy course, not a deep theory course: semigroups/monoids/groups/rings/semirings, bundled homomorphisms, units, scalar actions, modules, submodules, basic algebras over a commutative ring, and the foundational tensor/free-module viewpoint. It should teach the hierarchy and the APIs that everything else uses, but it should stop before the substantive theory of specific structures such as ring theory, linear algebra, or group theory. ([Lean Community][5])

## Algebra and group theory

5. **Group Theory I: algebraic, quotient, action, and finite group theory** — prereqs: **4** — **well covered**.
   This is the “standard serious group theory” course: groups and subgroup tests; cyclic and abelian groups; homomorphisms, kernels, images, and isomorphism theorems; cosets, normality, quotient groups, correspondence; actions, orbits, stabilizers, conjugation, class equation; permutation groups; Sylow theory; commutators, solvability, nilpotence, direct and semidirect products; free groups and presentations at the level needed for algebraic group theory. It is the prerequisite that later courses mean when they say “group theory.” ([Lean Community][6])

6. **Group Theory II: free groups, presentations, free products, amalgams, HNN extensions, wreath products, and Coxeter groups** — prereqs: **5** — **well covered**.
   This is the combinatorial-group-theory sequel. It should cover reduction and cyclic reduction in free groups, Nielsen–Schreier and Schreier-style subgroup results, presented groups as quotients of free groups, free products and normal forms, amalgamated products as pushouts, HNN extensions and Britton-type normal-form arguments, regular wreath products, and Coxeter systems/length/inversions as a capstone. It should **not** promise a full geometric-group-theory syllabus: Bass–Serre theory, hyperbolic groups, CAT(0) groups, automatic groups, boundaries, and small-cancellation theory would require substantial extension. ([Lean Community][7])

7. **Ring theory and polynomial algebra** — prereqs: **4** — **well covered**.
   This should cover semirings and rings as actual objects of study, ideals and quotient rings, Euclidean/PID/UFD style material where appropriate, polynomial and power-series style algebra, Jacobson/nil radicals, and the first substantial use of algebra maps and universal properties. It should stop before localization/Noetherianity/Krull dimension, which belong to commutative algebra. ([Lean Community][8])

8. **Linear Algebra I: vector spaces, bases, matrices, determinants, and linear maps** — prereqs: **4** — **well covered**.
   This is the standard first linear algebra course: modules over a field, bases and dimension, dual spaces, quotients, linear maps and matrix representations, determinants and invertibility, finite-dimensional structure, and the classical bridge between coordinate-free and matrix formulations. It should also include free modules and finitely generated modules over a PID at the point where mathlib already supports that story. ([Lean Community][9])

9. **Linear Algebra II: eigenvalues, characteristic/minimal polynomials, bilinear forms, quadratic forms, tensor/exterior/Clifford constructions** — prereqs: **8** — **well covered**.
   This course should include eigenspaces and generalized eigenspaces, characteristic and minimal polynomials, Cayley–Hamilton, triangularization-style results, bilinear and sesquilinear forms, orthogonality and adjoints, quadratic forms and real classification, tensor products, tensor algebras, exterior powers and exterior algebras, and Clifford algebras. This is where the subject becomes structural rather than computational. ([Lean Community][9])

10. **Commutative Algebra I: ideals, localization, Noetherianity, primary structure, and dimension** — prereqs: **7, 8** — **well covered**.
    This should be the serious commutative-algebra core: ideal operations and lattice structure, localization at submonoids and at primes, quotient constructions, Noetherian rings/modules, polynomial rings over Noetherian rings, Krull dimension, and the spectrum-level algebra that later feeds algebraic geometry. ([Lean Community][10])

11. **Commutative Algebra II: local methods, valuations, Kähler differentials, DVRs, Witt vectors, and arithmetic refinements** — prereqs: **10** — **well covered**.
    This is the advanced commutative-algebra continuation: local rings and localization-localization, valuation theory and valuation rings, discrete valuation rings, Kähler differentials and Jacobi–Zariski, and arithmetic gadgets such as Witt vectors. It should feel like the algebraic engine room for algebraic geometry and arithmetic geometry. ([Lean Community][11])

12. **Field theory and Galois theory** — prereqs: **7, 8** — **well covered**.
    This course should cover algebraic and separable extensions, splitting fields, algebraic closures, finite fields, Galois extensions, Galois groups, fixed fields, the Galois correspondence, and concrete examples such as cyclotomic and finite-field constructions. It can also include the model-theoretic ACF/Ax–Grothendieck bridge later, but that is not core to the course. ([Lean Community][9])

13. **Representation theory** — prereqs: **5, 7, 8** — **well covered**.
    This should cover monoid/group representations, characters, constructions on representations (sum, product, dual, tensor-style operations where appropriate), semisimplicity themes around Maschke, and the categorical viewpoint on `Rep k G`. It can continue into low-degree group cohomology if you want the course to point toward homological methods. ([Lean Community][9])

14. **Lie algebras, Lie modules, classical Lie algebras, and semisimple structure** — prereqs: **7, 8** — **well covered**.
    This course should include Lie rings and Lie algebras, Lie modules and morphisms, the adjoint action, ideals and radicals, semisimplicity, classical Lie algebras, and root/weight-oriented material to the extent mathlib’s current API supports it. It is algebraic Lie theory, not differential-geometric Lie groups. ([Lean Community][12])

15. **Homological algebra, derived categories, Ext, spectral objects, and snake-lemma technology** — prereqs: **9, 42** — **well covered**.
    This course should cover short complexes and exactness, homology, snake lemma, chain/cochain complexes, homotopy categories, derived categories as localization at quasi-isomorphisms, Ext in derived terms, distinguished triangles, t-structures, and spectral-object / spectral-sequence infrastructure. It is far beyond “first exposure to exact sequences.” ([Lean Community][13])

16. **Algebra topics seminar: free abelian groups, finite abelian duality, group extensions/localization, Jordan–Chevalley, semisimplicity, and other standalone algebra modules** — prereqs: depends on topic; usually **5, 7, 8, 12** — **well covered**.
    This is the spillover course for substantial algebra topics that are real mathlib subjects but do not justify their own full spine in this catalog: free abelian groups, finite abelian duality, Schur–Zassenhaus/Goursat/group extensions, monoid and Ore localization, Jordan–Chevalley, invariant basis number, special linear/symplectic groups, and similar standalone modules. ([Lean Community][6])

## Topology, analysis, and geometry

17. **General topology, uniform spaces, and compactness/connectedness technology** — prereqs: **2, 3** — **well covered**.
    This course should cover topological spaces, continuity, induced/coinduced topologies, open and closed maps, closure/interior/cluster points, Hausdorff and separation notions, compactness in open-cover and filter form, connectedness, compact-open topology, uniform spaces, completeness, and completion. It should be the main topological prerequisite for analysis and geometry. ([Lean Community][9])

18. **Metric spaces and quantitative topology** — prereqs: **17** — **well covered**.
    This is the metric continuation: balls and distances, Cauchy sequences, properness, compactness criteria, Lipschitz and Hölder maps, contraction mapping, Baire category, Arzelà–Ascoli, Hausdorff distance, and Gromov–Hausdorff space. It is not a separate foundational topology course in the traditional sense; it is the quantitative layer on top of 17. ([Lean Community][9])

19. **Topological groups, topological rings/modules, infinite sums, Haar measure, fiber bundles, vector bundles, and covering spaces** — prereqs: **5, 17** — **well covered**.
    This course should include topological groups and rings, topological modules, completions in the algebraic-topological setting, continuous group actions, infinite sums in topological groups, Haar measure on locally compact Hausdorff groups, topological fiber bundles, vector bundles, and covering-space infrastructure. It should stop before smooth manifolds. ([Lean Community][9])

20. **Real analysis and differential calculus** — prereqs: **8, 17, 18** — **well covered**.
    This should cover limits, continuity, differentiability in normed spaces, inverse and implicit function style material as supported, infinite series, special real functions, convexity/mean-value type estimates, and the multivariable calculus API used later by manifolds and analysis. The measure-theoretic side should be left for course 23. ([Lean Community][9])

21. **Complex analysis** — prereqs: **20** — **well covered**.
    This course should cover holomorphic/analytic functions, Cauchy integral formula, Liouville, maximum modulus, isolated zeros, analytic continuation, Schwarz lemma, removable singularities, the fundamental theorem of algebra, and the complex-analytic infrastructure behind modular forms and Fourier expansions. ([Lean Community][9])

22. **Functional analysis, operator theory, Banach algebras, Hilbert spaces, and C*-algebras** — prereqs: **9, 20** — **well covered**.
    This should include normed and Banach spaces, continuous linear maps and operator norms, Hahn–Banach and separation, dual and double-dual maps, Hilbert-space structure, spectral theory of self-adjoint operators, Banach-algebra spectra and spectral radius, and the current C*-algebra / continuous functional calculus material. ([Lean Community][9])

23. **Measure theory, integration, (L^p) spaces, and vector-valued integration** — prereqs: **17, 20, 8** — **well covered**.
    This course should cover measurable spaces and sigma-algebras, measurable functions, Borel structures, positive measures, Lebesgue and Hausdorff measure, Bochner integration, convergence theorems, Fubini, change of variables, convolution, and the construction and completeness of (L^p) spaces. ([Lean Community][9])

24. **Probability theory and stochastic processes** — prereqs: **23** — **well covered**.
    This should cover probability measures, independence, conditional probability and conditional expectation, distributions and densities, moments and variance, convergence in probability / a.s. / distribution / (L^p), Markov and Chebyshev inequalities, strong law of large numbers, martingales, stopping times, and optional stopping. ([Lean Community][9])

25. **Dynamics and ergodic theory** — prereqs: **17, 23, 24** — **needs extension**.
    A good current course can cover fixed and periodic points, Birkhoff sums and averages, measure-preserving and quasi-measure-preserving maps, ergodicity/conservativity, topological entropy for subsets, and the mean ergodic theorem in Hilbert spaces. A **standard broader** dynamics/ergodic-theory course would still want more than the present mathlib surface offers, so I would not call the area fully saturated yet. ([Lean Community][9])

26. **Manifolds, tangent bundles, vector fields, Lie groups, and differential topology** — prereqs: **9, 17, 20** — **well covered**.
    This should cover manifolds with corners/boundary, smooth maps, immersions and embeddings, products and disjoint unions, tangent bundles and tangent maps, vector fields and Lie brackets, integral curves and their existence/uniqueness results, Lie groups as manifolds, and the manifold-side infrastructure for later geometry. ([Lean Community][9])

27. **Affine, Euclidean, convex, and classical geometric constructions** — prereqs: **8, 17** — **well covered**.
    This course should include affine spaces and affine subspaces, barycenters and affine span, Euclidean geometry with angles and orthogonality, simplices and centroids, convex cones and dual cones, and the linear-algebraic side of geometry. It should not try to subsume manifolds or algebraic geometry. ([Lean Community][9])

28. **Fourier analysis, distributions, and selected differential-equation material** — prereqs: **20, 22, 23** — **well covered**.
    This course should cover Fourier transforms and inversion, Parseval/Riemann–Lebesgue style results, Schwartz space and tempered distributions, convolution/regularization, and the ODE / flow material that mathlib already connects to analysis and manifolds. ([Lean Community][9])

## Number theory and combinatorics

29. **Elementary number theory** — prereqs: **7** — **well covered**.
    This course should cover divisibility, gcd/lcm, primes and factorizations, congruences, Euler totient/arithmetic functions at an elementary level, quadratic residues and Legendre symbol basics, Pell-type material, and classical proofs about integers and finite fields. ([Lean Community][9])

30. **Multiplicative and analytic number theory** — prereqs: **29, 21, 23** — **well covered**.
    This should cover arithmetic functions, Dirichlet-style multiplicative identities, Bernoulli numbers, analytic expansions used in Eisenstein/q-expansion work, and classical analytic theorems that mathlib already formalizes in number-theoretic contexts. It is not “all analytic number theory,” but it is a real course. ([Lean Community][9])

31. **Algebraic number theory, p-adics, local fields, cyclotomic fields, and modular forms** — prereqs: **10, 12, 21, 29** — **well covered**.
    This course should cover number fields and rings of integers, units and infinite places, canonical embeddings, discriminants and finiteness results, cyclotomic extensions and cyclotomic characters, (p)-adic numbers and integers, local-field structure, and modular forms at the level of Eisenstein series, q-expansions, congruence/arithmetic subgroups, Dedekind eta, Delta, and Petersson-related infrastructure. ([Lean Community][14])

32. **Combinatorics and graph theory** — prereqs: **1, 2** — **well covered**.
    This should cover pigeonhole principles, Hall’s marriage theorem and transversals, Catalan/Bell/Dyck enumerative material, set-family inequalities, simple graphs, matchings, adjacency matrices, strongly regular graphs, Turán, regularity and removal/counting lemmas at the level already in mathlib. It should stop before additive combinatorics and the deeper Ramsey material if you want a cleaner first course. ([Lean Community][9])

33. **Advanced combinatorics: Ramsey theory, additive combinatorics, matroids, quivers, and related discrete structures** — prereqs: **32, 5** depending on topic — **well covered**.
    This should cover van der Waerden / Hales–Jewett / Hindman style Ramsey theorems, additive combinatorics topics such as Roth, corners, doubling, Ruzsa, Plünnecke–Petridis, Cauchy–Davenport, EGZ, additive energy, and the structural combinatorics side of matroids and quivers. This is where the discrete side stops being “counting” and becomes theorem-heavy modern combinatorics. ([Lean Community][9])

## Logic, computation, and set theory

34. **Computability, recursive functions, Turing machines, automata, and formal languages** — prereqs: **1, 2** — **well covered**.
    This course should cover primitive recursion and partial recursion, computable functions, Turing machines, halting/Rice-style undecidability, regular languages and automata, context-free grammars/languages, and the bridge between syntax and machine models. Basic complexity content can be folded into the end. ([Lean Community][9])

35. **Model Theory I: syntax, semantics, satisfiability, compactness, Löwenheim–Skolem, and types** — prereqs: **2** — **well covered**.
    This should cover first-order languages, terms, formulas, theories, structures, satisfaction, satisfiability, substructures, definable sets, elementary embeddings, compactness, Löwenheim–Skolem, and complete types. This is a substantial and coherent first model-theory course already. ([Lean Community][9])

36. **Model Theory II: ultraproducts, ACF, Presburger arithmetic, graph-model examples, and Fraïssé-style directions** — prereqs: **35** — **well covered**.
    This continuation should cover ultraproducts and Łoś’s theorem, the theory of algebraically closed fields and completeness/Lefschetz-type results, Presburger arithmetic and semilinear definability, concrete language/theory examples in graphs and ordered structures, and whatever Fraïssé-style material you want to build on top of the existing infrastructure. ([Lean Community][15])

37. **Set Theory I: ordinals, cardinals, ordinal arithmetic, and Cantor normal form** — prereqs: **2, 3** — **well covered**.
    This should cover the construction and order theory of cardinals and ordinals, ordinal arithmetic, cardinal arithmetic, finite/countable cardinals, principal ordinals, fixed points of normal ordinal functions, and Cantor normal forms / notation systems. It is a real transfinite course, not just a short appendix to logic. ([Lean Community][9])

38. **Set Theory II: ZFC sets, classes, rank, models of ZFC, and game/nimber side topics** — prereqs: **37** — **well covered**.
    This course should cover the ZFC model built inside Lean, pre-sets and quotients to ZF-sets, classes, rank, and the “internal set-theory” API. It can also absorb the existing set-theoretic game theory and nimber material as an advanced unit, since that material sits naturally in the same branch even though it is mathematically a different course. ([Lean Community][16])

39. **Descriptive set theory** — prereqs: **17, 37** — **needs extension**.
    I would treat this as extension territory. You can build pieces around Polish-space and countability infrastructure, but a standard descriptive-set-theory course would require much more than current mathlib visibly supplies as a dedicated branch. ([Lean Community][6])

40. **Metamathematics, Gödel coding, incompleteness, and proof-theoretic arithmetic** — prereqs: **34, 35, 38** — **needs extension**.
    Mathlib has enough adjacent machinery to make this a plausible future project, but not enough for me to call a standard incompleteness/metamathematics course “already covered.” It is a prime extension target, not a course I would currently mark as library-complete. ([Lean Community][16])

## Category theory and the highest-level geometric subjects

41. **Category Theory I: categories, functors, natural transformations, Yoneda, and basic examples** — prereqs: **2, 4** — **well covered**.
    This should cover categories, functors, natural transformations, equivalences, opposite categories, the category of types and algebraic examples, Yoneda, comma-style constructions, and the base language for all higher categorical material in mathlib. ([Lean Community][9])

42. **Category Theory II: limits, adjunctions, monads, monoidal categories, abelian categories, and localization technology** — prereqs: **41** — **well covered**.
    This should include limits and colimits, filteredness, adjunctions and monads, monoidal and braided structure, abelian categories and injectives, localization-style constructions, and the categorical infrastructure used by homological algebra, sheaves, and algebraic geometry. ([Lean Community][9])

43. **Sheaves, Grothendieck topologies, coherent topologies, sheafification, and topoi** — prereqs: **17, 42** — **well covered**.
    This course should cover presheaves and sheaves on sites, Grothendieck topologies, coherent/regular/extensive topologies, sheafification and compatibility results, sheaf Hom, hypercovers as they appear in the API, and the topoi side at least up to subobject classifiers and related structure. ([GitHub][17])

44. **Algebraic topology: fundamental groupoids, singular homology, simplicial sets, Dold–Kan, model categories, and quasicategories** — prereqs: **17, 42** — **needs extension**.
    Mathlib already supports a serious algebraic-topology course built around fundamental groupoids, simply connectedness, induced maps, singular chain complexes and homology, simplicial sets, Dold–Kan, model-category infrastructure, and quasicategories. I still mark the area **needs extension** because a standard broad algebraic-topology curriculum would normally want more homotopy/cohomology breadth than is currently visible as a mature unified surface. ([Lean Community][18])

45. **Algebraic Geometry I: affine schemes, Spec, structure sheaf, locally ringed spaces, and schemes** — prereqs: **11, 42** — **well covered**.
    This should cover prime spectrum, Zariski topology, ringed/presheafed/sheafed/locally ringed spaces, `Spec` as a functor, the structure sheaf, affine schemes, and the construction and basic theory of schemes and their morphisms. That core is already substantial. ([Lean Community][9])

46. **Algebraic Geometry II: projective spectrum, morphism properties, descent, étale/smooth/proper theory, sites over schemes, and higher sheaf technology** — prereqs: **45, 43, 15** — **needs extension**.
    This continuation should cover projective spectrum, ideal sheaves and subschemes, the major morphism properties (finite type/presentation, flat, integral, proper, smooth, étale, weakly étale, etc.), descent and base change, big/small Zariski and étale/pro-étale/fpqc-style sites, and the beginnings of hypercover/sheaf technology on schemes. The branch is already deep, but the docs themselves still advertise parts of the site machinery as groundwork for future étale-cohomological applications, so I would not call the area finished. ([Lean Community][6])

47. **Condensed mathematics** — prereqs: **43, 23, 42** — **needs extension**.
    The current branch clearly supports a real advanced topics course on condensed sets and condensed modules, discrete/light condensed objects, solid modules, and AB axioms for condensed module categories. I still mark it **needs extension** because the subject as mathematicians usually mean it is much broader than the current branch. ([Lean Community][19])

48. **Information theory and coding** — prereqs: **24, 34** — **needs extension**.
    Right now this is best scoped as a focused course on Hamming spaces and minimum-distance ideas, uniquely decodable codes and Kraft–McMillan, and Kullback–Leibler divergence / Gibbs-style inequalities. That is enough for a good short advanced course, but not for a standard full information-theory curriculum with entropy, channel capacity, rate-distortion, and coding theorems, so I mark it **needs extension**. ([Lean Community][20])

49. **Functor / applicative / monad / traversable patterns used across mathlib** — **basic** — **well covered**.
    This is the one non-mathematical add-on I would keep in the catalog because it matters in practice. It should cover the core `Control` abstractions and the places where they interact with data structures and proof engineering in mathlib. It is not a mathematics course, but it is real library literacy. ([GitHub][1])

[1]: https://github.com/leanprover-community/mathlib4 "GitHub - leanprover-community/mathlib4: The math library of Lean 4 · GitHub"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html"
[4]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/CompleteLattice/Defs.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/CompleteLattice/Defs.html"
[5]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html"
[6]: https://leanprover-community.github.io/mathlib4_docs/Mathlib "https://leanprover-community.github.io/mathlib4_docs/Mathlib"
[7]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FreeGroup/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FreeGroup/Basic.html"
[8]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Basic.html"
[9]: https://leanprover-community.github.io/mathlib-overview.html "Mathematics in mathlib"
[10]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Lattice.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Lattice.html"
[11]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/LocalizationLocalization.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/LocalizationLocalization.html"
[12]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Basic.html"
[13]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ShortComplex/ShortExact.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ShortComplex/ShortExact.html"
[14]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Basic.html"
[15]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Ultraproducts.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Ultraproducts.html"
[16]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html"
[17]: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/CategoryTheory/Sites/Grothendieck.lean "https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/CategoryTheory/Sites/Grothendieck.lean"
[18]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html"
[19]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Condensed/Basic.html?utm_source=chatgpt.com "Mathlib.Condensed.Basic"
[20]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/InformationTheory/Hamming.html?utm_source=chatgpt.com "Mathlib.InformationTheory.Hamming"
[21]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coxeter/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coxeter/Basic.html"


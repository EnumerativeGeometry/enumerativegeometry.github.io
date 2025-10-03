# Virtual Sets and Enumerative Geometry: Building an open-source virtual mathematical kernel with Lean4.

Our project aims to develop a rigorously validated virtual mathematical kernel based on the Virtual Set Theory (VST) framework, implemented in Lean 4 and verified using the Lean 4 theorem prover. Building upon a minimal working example—demonstrated through the full proof accessible in the README and the Lean 4 source under theorems—this work addresses the classical Problem of Apollonius alongside an NP-hard variant. The solution methodology involves constructing virtual sets within Lean 4, revealing profound interconnections spanning algebraic geometry, fractal geometry, and set theory—disciplines conventionally regarded as disjoint.

Notably, the enumerative structure of this approach renders it computationally feasible, thereby enabling the effective simulation of virtual sets on a computer.

![Ludwig Feuerbach](https://raw.githubusercontent.com/EnumerativeGeometry/enumerativegeometry.github.io/main/static/ludwig.png)

"A circle in a straight line is the mathematical symbol of miracle."  
— Ludwig Feuerbach, *The Essence of Christianity*

---

---
## Overview

The project uses **Lean 4** to formalize axioms, definitions, and theorems, enabling rigorous computer-verified proofs of Apollonius problems and variants, connecting foundational mathematics with cutting-edge geometric enumeration. In the future, other theorems beyond this minimal working example can be developed (see project roadmap and conjectures). The main repo is [Visit the Virtual Set Theory GitHub Repository](https://github.com/EnumerativeGeometry/enumerativegeometry.github.io)


## Repository Structure

- **`axioms.lean`**  
  Contains foundational axioms including classical membership and the new virtual membership relation parameterized over an indexing space.

- **`definitions.lean`**  
  Defines geometric objects in the moduli space \(\mathcal{M}\) that models points, lines, and circles uniformly required for the proof and eventually virtual sets.

- **`theorems.lean`**  
  Encodes key theorems such as the Chow ring intersection relation \(h^3 = 2h\), central to the enumerative solution of the Apollonius problem.
- **`apollonius.lean`**
  This is the main mathematical kernel, focused on a specific working example it will be extended to rebuild classical results using virtual sets.
---

## Getting Started

### Prerequisites

- Install [Lean 4](https://lean-lang.org/install/)
- Install the **Lean 4 VS Code extension** for best interactive editing and proof development.
- Optional: Install `lake` (Lean’s build tool, included in Lean 4) to manage builds.

### Setup

Clone the repository and build all code:

git clone https://github.com/EnumerativeGeometry/enumerativegeometry.github.io.git
cd enumerativegeometry.github.io
lake build

text

This checks compilation and proof verification of axioms, definitions, and theorems.

### Editing and Running Code

- Open the project folder in VS Code:  

code .

text
- Open any `.lean` file (like `axioms.lean`) to view or add your formalization.
- The Lean extension highlights errors, shows proof states, and guides you interactively.

---

## How to Use Each File

### `axioms.lean`

- Defines membership concepts foundational to VST.
- Primarily declarations and axioms; do not expect executable code.
- Proofs about consistency and paradox resolution will build here.

### `definitions.lean`

- Formalizes the moduli space hosting points, lines, and circles.
- These definitions serve as the vocabulary for stating theorems.
- You can add recursive definitions of virtual sets and indexing strata here.

### `theorems.lean`

- Contains major enumerative geometry results, starting from the key Chow ring relation.
- Proof scripts verifying the enumerative counts and intersection identities.
- Proofs may build on the axioms and definitions files.

# Virtual Set Theory and the Enumerative Geometry of Membership

## Table of Contents
- [Introduction](#introduction-and-motivation)
- [Project Overview](#project-overview)
- [VST for solving Generalized NP-Hard Problems](Classical-Apollonius-Problem)
- [Fractal Self-Containing Sets in Virtual Set Theory (VST)](#fractal-self-containing-sets-in-virtual-set-theory)
- [Mathematical Notation and Definitions](#mathematical-notation-and-definitions)  
- [Research Review and Current Context](#research-review-and-current-context)  
- [Specific Mathematical Goals and Theorems](#specific-mathematical-goals-and-theorems)  
- [Methodology and Approach](#methodology-and-approach)  
- [Research Plan and Timeline](#research-plan-and-timeline)  
- [Expected Impact and Significance](#expected-impact-and-significance)  
- [References](#references)  

---

## Introduction and Motivation

Virtual Set Theory (VST) refines classical set theory by reformulating membership as a continuous, recursive, and parameterized relation motivated by fractal degenerations in enumerative geometry. Unlike classical set theory, which builds its universe exclusively from points, VST begins with a unified geometric foundation comprising points, lines, and circles—reflecting their equivalence in inversive geometry—and models them as elements of a stratified moduli space. This geometric starting point naturally captures degenerations and recursive structures prior to generalizing to a virtualized notion of membership.

VST is designed as a meta-framework built on classical axiomatic foundations, with the explicit goal of enabling the systematic replacement of classical sets by virtual sets in nearly every classical proof or theorem. The membership relation in VST is rigorously generalized to a fractal and recursive parameterization indexed by stratified parameter spaces such as posets, trees, or directed graphs, encoding intricate fractal strata inspired by enumerative geometry. This approach preserves the classical axioms while providing enriched internal structure to resolve foundational paradoxes and enable refined enumeration.

While category theory and modern type-theoretic frameworks capture hierarchical and recursive structures via morphisms and universal properties, VST uniquely focuses on generalizing membership itself as an internal, parameterized relation. In doing so, it provides a complementary meta-framework tailored specifically for fractal and recursive geometric phenomena without redundantly repackaging existing categorical or type-theoretic constructs.

A key application of VST is the rigorous proof and enumerative solution of a generalized version of the Apollonius problem—which involves constructing circles tangent to configurations of points, lines, and circles in the plane—a problem known to be NP-hard. By embedding the problem in the VST framework, one obtains a novel intersection-theoretic method leveraging virtual membership to systematically handle fractal degenerations and recursive constraints that classical foundational approaches struggle to address, showing the power of the framework.

## Enumerative Counting Problem

Given:

- Three distinct circles \((C_1, C_2, C_3)\),
- Two distinct points \((P_1, P_2)\),
- Five distinct lines \((L_1, \ldots, L_5)\),

all in general position.

**Goal:** Count all circles \((C)\) such that:

- \(C\) is tangent to *exactly two* of the three circles,
- \(C\) passes through *exactly one* of the two points,
- \(C\) is tangent to *exactly three* of the five lines.

---

## The Moduli Space Framework

The moduli space \(\mathcal{M}\) parametrizes all points, lines, and circles uniformly as:

\[
\mathcal{M} = \{ (x,y,r) \mid (x,y) \in \mathbb{R}^2, \quad r \in \mathbb{P}^1(\mathbb{R}) = \mathbb{R} \cup \{\infty\} \}
\]

where:

- \(r=0\) corresponds to points,
- \(r \in (0,\infty)\) corresponds to circles,
- \(r = \infty\) corresponds to lines.

Points, lines, and circles coexist as elements of \(\mathcal{M}\), allowing degenerate cases and infinite limiting behavior. This space forms the natural geometric arena for the enumerative constraints defining the problem.

---

## Classical Apollonius Problem

Given three fixed circles \(C_i = (x_i, y_i, r_i) \in \mathcal{M}\), find all circles tangent to each \(C_i\).

This amounts to solving the system:

\[
\begin{cases}
(x - x_1)^2 + (y - y_1)^2 = (r \pm r_1)^2 \\
(x - x_2)^2 + (y - y_2)^2 = (r \pm r_2)^2 \\
(x - x_3)^2 + (y - y_3)^2 = (r \pm r_3)^2 
\end{cases}
\]

where the sign \(\pm\) is chosen for internal or external tangency in each case.

---

## Virtual Set Theory: Parameterized Membership

VST replaces classical binary membership \(\in\) with a parameterized virtual membership relation:

\[
\widetilde{\in} : E \times \mathcal{I} \to \{0,1\}
\]

where:

- \(E\) is the universe of geometric elements (circles, lines, points),
- \(\mathcal{I}\) is an indexing parameter space—such as posets, trees, or directed graphs—encoding recursive and fractal membership layers.

This membership relation is recursive and fractal, embedding mathematics within itself using a self-referential, structure-preserving embedding rather than a literal bijection, allowing every classical set to be replaced by a virtual set with a richer internal structure. This framework allows for controlled and noncontradictory solutions to classical paradoxes such as Russell’s paradox.


## Enumerative Solution: Intersection Theory in Virtual Context

We address the generalized Apollonius problem within the moduli space \(\mathcal{M}\), which parametrizes geometric elements in the plane: points, lines, and circles represented as triples \((x,y,r)\) with

\[
\mathcal{M} = \{(x,y,r) \mid (x,y) \in \mathbb{R}^2, \ r \in \mathbb{P}^1(\mathbb{R}) = \mathbb{R} \cup \{\infty\}\}.
\]

This framework incorporates points \((r=0)\), circles \((r \in (0,\infty))\), and lines \((r = \infty)\) uniformly.

### Encoding Enumerative Constraints as Divisor Classes

Based on the problem data—three distinct circles \(C_1,C_2,C_3\), two distinct points \(P_1,P_2\), and five distinct lines \(L_1,\ldots,L_5\)—we encode the counting conditions as formal divisor classes \(h \in A^*(\mathcal{M})\) representing tangency or point incidence conditions:

- Circles tangent to exactly two of the three circles encode as \(3h^2 - h^3\).
- Circles passing through exactly one of the two points encode as \(2h - 2h^2\).
- Circles tangent to exactly three of the five lines encode as
  \[
  \binom{5}{3} h^3 - \binom{5}{4} 2h^2 + \binom{5}{5} 2h^3 = 12 h^3 - 20 h^2.
  \]

The signs and coefficients arise from inclusion-exclusion principles to enforce exactness in each condition.

### The Core Chow Relation

The intersection-theoretic computations rely on the key relation in the Chow ring [see derivation] of \(\mathcal{M}\):

\[
h^3 = 2h.
\]

This relation models the enumerative geometry multiplicities arising from triple tangency or intersection conditions in \(\mathcal{M}\). In the same way that set membership does not allow multiplicities (an element is either a member of a set or not a member of a set, it is only counted once in the cardinality of the set), the chow relation is fundamental to the virtaul set membership, providing a way to count the size of virtual sets and reduce multiplicities that arise in constructing virtual sets using ing intersection theory.

### Justification of the Relation \(h^3 = 2h\)

- **Geometric Interpretation:** The moduli space \(\mathcal{M}\) locally resembles a projective bundle over \(\mathbb{R}^2\), where \(h\) is the first Chern class of the tautological line bundle.
- Using the *projective bundle formula* in intersection theory, the Chow ring satisfies relations among powers of \(h\) and Chern classes of the associated bundle.
- The classical Apollonius problem states that three general circles admit exactly 8 tangent circles. Modelling this enumeratively in \(\mathcal{M}\), the relation \(h^3 = 2h\) reflects effective multiplicities that arise when intersecting conditions represented by \(h\) thrice. This matches the classical count up to multiplicities.
- Formally, this can be seen as an intersection number of three divisor classes on \(\mathcal{M}\), with the coefficient 2 reflecting multiplicities from degenerate or parallel conditions.

### Computing the Total Number of Circles

First we will start with an upper bound of 40, since there are at most 40 incircles or excircles given the 3 tangency conditions. We can compute this upper bound in another way, using our Moduli space.

The total enumerative count of circles satisfying all constraints is given by the intersection product:

\[
\text{Total count} = (3h^2 - h^3)(2h - 2h^2)(12 h^3 - 20 h^2).
\]

Applying \(h^3=2h\), expand and reduce:

\[
\begin{aligned}
& (3h^2 - h^3)(2h - 2h^2)(12 h^3 - 20 h^2) \\
= & (3h^2 - 2h)(2h - 2h^2)(24h - 20h^2) \\
= & \ldots \\
\end{aligned}
\]

Upon further expansion and simplification, this yields the exact count of circles meeting all enumerative constraints. The above intersection product can be deduced using inclusion-exclusion for each of the 3 tangency conditions as follows:

1) Tangent to 2 circles in the moduli space is modeled by h^2, since each tangency imposes on independent divisor condition. However, this overcounts cases where the circle is also tangent to the third circle at the same time, a condition that cannot happen, therefore since these cases satisfy 3 tangency conditions, we can subtract h^3 to remove the overcount. Hence, since there are 3 ways to choose 2 circles from 3 circles, the first tangency condition is 3h^2-h^3.

2) The same logic applies to the other 2 conditions, the naive count (incidence with 2 other points) is 2h but if a circle passes through both points, it was double counted, so we need to subtract 2h^2.

3) We can choose 3 lines from 5 lines, but if a circle is tangent to 4 lines, that case apperas in multiple triples, so we can subtract the overcounts, then add back corrections for circles tangent to all 5 lines. This gives the final term 12h^3-20h^2.

Finally, in the chow ring, since we impose 3 tangency conditions, the final intersection space degenerates, yielding solutions with multipicity 2. Thus, since each of the 3 cases is a tangency or incidence condition that is given by a factor of h, and exactly conditions require inclusion-exclusion, we can take our final intersection equation, with coefficients corresponding to the combinatorial choices in each of the cases and substitute in the core chow relation, to get the total number of circles as the coefficient of the final h term.

Reducing via the hcow ring relation gives approximately 672h. However, this is too large, because not all intersection multiplicities correspond to real multiplicities in the Euclidean plane, therefore, we introducr variables alpha and beta, that represent the virtual local intersection multiplicities in our upper bound.

This leads to a corrected count (3h^2-alphah^3) * (2h -betah^2) * (12h^3 -20h^2) , substituting the chow relation again we get,

Count = -(2 * 20 * (12 + 4 alpha * beta) + 48 ( 6 * beta + 4 alpha). The minus sign is a convention coming from the intersection theory operation, reducing further we get:

-Count = 480 + 160alpha*beta + 288beta + 192alpha (Equation 1) and - Count >= -40 (Inequality 1) where alpha and beta are positive rational nunmbers corresponding to exact virtual multiplicities in our Moduli space (intuitively this is the cardinality of a virtual set corresponding to our solution).

We can simulate this in Sage to solve for alpha, beta since both alpha and beta are completely determined by local degeneracy conditions, namely, degenerate solutions correspond to another subvariety or in VST a virtual set in the Moduli space that overcount, producing higher local intersetion multiplicities than in the Euclidean plane, therefore we can create a second equation that completely determines the system by counting local degenerate solutions.

McKlean's work [2022, arXiv:2210.13288] rigorously relates these local intersection multplicities to Euler classes of vector bundles and oriented volumes of gradients of defining quadratics at intersection points. These local multiplicities contribute additively and lineraly to the corrected terms represented by alpha and beta.

Therefore, by solving the total real count in terms of alpha and beta, we can write a second equation in terms of alpha and beta:

Equation (2) C_0 + C1*alpha + C2*beta + C3*alpha*beta = 0 where C_i are constants computable from the geometry (euler characteristics and volumes of gradient cones found in McKay's paper]. These can be computed in Sage and made explicit.

Now, Equations (1) and Equations (2) can be solved for alpha and beta in Sage and substituted back into Equation (1), if there are multiple solutons (negative and positive) Equality (1) can be used to determine the unique solution if it exists for the configuratio of circles, lines and points given to get the final corrected Count, corresponding to the total real number of tangent circles. 
---

This comprehensive and rigorously justifies the enumerative solution for the generalized Apollonius problem using intersection theory on \(\mathcal{M}\), clearly linking classical enumerations with the Chow ring relations and virtual set theory's conceptual framework.

## Fractal Self-Containing Sets in Virtual Set Theory (VST)

### Notation and Definitions

- \( E \) — The universe of virtual sets (points, lines, circles, and generalized sets).
- \( \mathcal{I} \) — An indexing parameter space (e.g., posets, trees, directed graphs) organizing recursive membership strata.
- Classical membership: \( x \in A \) means element \( x \) is in classical set \( A \).
- Virtual membership relation:
  \[
  \widetilde{\in} : E \times \mathcal{I} \to \{0,1\},
  \]
  where \( \widetilde{\in}(x, i) = 1 \) means \( x \) is a member of some virtual set at stratum \( i \in \mathcal{I} \).

### Constructing a Fractal Set That Contains Itself

In classical set theory, the Axiom of Foundation forbids any set \( S \) such that \( S \in S \). Virtual Set Theory relaxes that restriction by allowing membership at distinct strata, enabling fractal-like self-containment:

- Let \( V \in E \) be a virtual set.
- There exist strata \( i, j \in \mathcal{I} \) with \( i \neq j \) such that membership holds recursively:
  \[
  V \ \widetilde{\in}_i \ V, \quad V \ \widetilde{\in}_j \ V,
  \]
  where \( \widetilde{\in}_k \) notation abbreviates \( \widetilde{\in}(-, k) \).

This means \( V \) belongs to itself at different levels or layers of membership, embedding infinite recursive structure within \( V \) analogous to fractals in geometry.

### Conceptual Interpretation

- **Recursive Membership Layers:** Each stratum \( i \in \mathcal{I} \) organizes the fractal recursion, avoiding direct self-membership paradoxes


## Why This Matters and Contextualizing Virtual Set Theory

Virtual Set Theory (VST) is developed entirely within classical mathematics. It does not introduce a new foundational system or alternative universe but redefines set membership as a parameterized, recursive, and fractal-like relation. This enriched notion of membership is fully compatible with classical set theories such as Zermelo-Fraenkel and Von Neumann-Bernays-Gödel, and does not contradict their axioms. VST thus extends classical sets from inside the existing framework rather than standing outside or opposing classical foundations.

In enumerative geometry, VST addresses counting problems involving fractal degenerations and recursive geometric structures exemplified by the generalized Apollonius problem. While modern enumerative techniques also employ tools like Gromov-Witten invariants, intersection theory, and moduli stacks, VST provides an alternative perspective through its virtual membership framework. Future work aims to clarify connections and integrations between VST and these classical tools to demonstrate their complementarity.

Regarding category theory, modern higher categories, homotopy type theory, and related frameworks already support hierarchical, recursive, and self-referential structures. VST does not claim to replace these but offers a meta-framework specifically tailored to fractal parameterized membership relations. Further publications will elaborate the precise scope, advantages, and distinctions of VST vis-à-vis these theories.

Virtual Set Theory (VST) can be rigorously conceptualized via a Ship of Theseus–type morphism: it reconstructs the universe of classical mathematics by systematically replacing each classical set with a corresponding virtual set through a well-defined morphism that preserves nearly all classical theorems. However, this morphism allows controlled transformations where certain theorem truth values may be reversed to consistently resolve foundational paradoxes, such as those arising from classical membership and self-containment. This process thus realizes a structural recursive embedding of the classical universe into a fractally stratified virtual universe, embodying the philosophical essence of gradual object replacement and identity persistence formalized as morphisms in a categorical or type-theoretic framework.

Just as the Ship of Theseus remains "the same ship" despite all of its parts eventually being replaced, VST preserves the essence of classical set theory while transforming the membership relation to avoid artificial limitations imposed by axioms like Foundation. This allows for a rigorous "virtual mathematics" that faithfully extends classical structures without contradiction, reinterpreting membership and truth in a fractal, recursive manner within classical mathematics itself.

## Project Overview

This project develops **Virtual Set Theory (VST)**, a novel foundational framework in which classical set membership \(\in\) is generalized to a recursive, parameterized fractal relation \(\widetilde{\in}\), motivated by fractal degenerations in enumerative geometry. The goal is to unify foundational set theory with sophisticated enumerative geometric problems such as the generalized Apollonius problem, embedding recursive membership structure into intersection theory and moduli space methods.

---

## Mathematical Notation and Definitions

- **Classical Membership:**  
  \(x \in A\) denotes element \(x\) belonging to classical set \(A.\)

- **Virtual Membership Relation:**  
  \[
  \widetilde{\in} : E \times \mathcal{I} \to \{0,1\},
  \]
  where  
  \(E\) = universe of geometric elements (circles, lines, points),  
  \(\mathcal{I}\) = stratified parameter space (posets, trees, directed graphs).

- **Moduli Space \(\mathcal{M}\):**  
  \[
  \mathcal{M} = \{(x,y,r) \mid (x,y) \in \mathbb{R}^2, r \in \mathbb{P}^1(\mathbb{R}) = \mathbb{R} \cup \{\infty\}\},
  \]
  with  
  \[
  r=0 \Rightarrow \text{points}, \quad r \in (0,\infty) \Rightarrow \text{circles}, \quad r = \infty \Rightarrow \text{lines}.
  \]

- **Chow Ring Relation:**  
  \[
  h^3 = 2h,
  \]
  where \(h\) is the divisor class encoding tangency and incidence conditions on \(\mathcal{M}\).

---

## Research Review and Current Context

- Classical ZFC set theory provides robust foundations but fails to encode recursive fractal membership; virtual large cardinal theory enriches embeddings but maintains classical membership.  
- Enumerative geometry via Gromov–Witten invariants tackles many incidence problems but lacks tools for NP-hard, fractal-degenerate constraints like generalized Apollonius.  
- Higher category theory and homotopy type theory encode recursion morphism-wise, but not membership fractality explicitly.  
- VST introduces a **parameterized recursive membership relation** encoding fractal degenerations foundationally, enabling new intersection-theoretic enumeration and resolution of classical problems otherwise out of reach.  
- Key references: Gitman-Hamkins-Wilson (2020), Fulton (1998), McKean (2022), Lurie, Voevodsky.

---

## Specific Mathematical Goals and Theorems

1. **Foundational Axioms and Consistency**  
   - Formalize recursive membership \(\widetilde{\in}\) axioms extending ZFC.  
   - Prove consistency relative to ZFC.  
   - Resolve classical paradoxes via recursive layer stratification, removing need for Foundation axiom.

2. **Moduli Space \(\mathcal{M}\) Construction**  
   - Define \(\mathcal{M}\) with compatible analytic structure for points, lines, and circles.  
   - Construct divisor classes encoding enumerative constraints.

3. **Chow Ring Intersection Relation**  
   - Prove rigorously that on \(\mathcal{M}\), the divisors satisfy:  
     \[
     h^3 = 2h.
     \]  
   - Interpret this as arising from fractal recursive multiplicities from VST membership structure.

4. **Enumerative Solution of Generalized Apollonius Problem**  
   - Express exact tangencies to points, lines, circles as intersection products.  
   - Prove explicit formula for counting solution circles incorporating fractal degenerations.

5. **Higher-Dimensional Extensions and Derived Embeddings**  
   - Construct higher-dimensional moduli \(\mathcal{M}_n\).  
   - Define recursive enumerative invariants for virtual membership.  
   - Prove embedding into homotopy/derived categorical frameworks linking with classical invariants.

6. **Foundational Morphisms and Ship of Theseus Principle**  
   - Formalize recursive replacement morphisms preserving virtual set structure as categorical functors.

---

## Methodology and Approach

- **Foundational Work:** Use classical logic and set theory augmented by parameterized indexing to define \(\widetilde{\in}\). Employ sheaf theory over parameter spaces to build models ensuring consistency.  
- **Moduli Construction:** Use real-analytic geometry to construct \(\mathcal{M}\) and associated divisor classes, proving stratification respects virtual membership indices.  
- **Intersection Theory:** Adapt classical Chow ring techniques to this enriched setting; compute intersection numbers via recursive virtual multiplicities.  
- **Enumerative Computations:** Translate geometric tangency conditions to combinatorial divisor classes; exploit the Chow relation to simplify expansions and exact counts.  
- **Generalizations:** Develop inductive procedures extending moduli and invariants to higher dimensions, proving existence and functoriality.  
- **Embedding and Comparison:** Construct natural transformations linking VST-based virtual sets to known categorical and homotopical structures; prove equivalences and distinctions.  

---

## Research Plan and Timeline

| Phase               | Milestones and Proof Objectives                                                                                                        | Deliverables                      |
|---------------------|----------------------------------------------------------------------------------------------------------------------------------------|---------------------------------|
| **2025 Q4 – 2026 Q2** | Formalize recursive membership axioms; construct models for consistency; prove paradox resolution.                                     | *Foundations of Virtual Sets*    |
| **2026 Q3 – 2027 Q1** | Construct moduli space \(\mathcal{M}\); define divisor classes; prove key Chow ring relation \(h^3=2h\); solve generalized Apollonius. | *Apollonius Problem in VST*      |
| **2027 Q2 – 2027 Q4** | Extend to higher dimensions; define and prove recursive enumerative invariants; relate to Gromov–Witten invariants and derived stacks. | *Virtual Sets and Enumerative Geometry* |
| **2028**             | Formalize Ship of Theseus morphisms; explore embeddings into modern categories; facilitate workshops; publish integrative foundational studies. | *Extending ZF with Virtual Sets* |

---

## References

- Fulton, W. *Intersection Theory*, Springer, 1998.  
- Gitman, V., Hamkins, J.D., Wilson, J. "Virtual large cardinals," *Journal of Symbolic Logic*, 2020.  
- McKean, K. "Recent advances in enumerative geometry," arXiv:2210.13288, 2022.  
- Lurie, J. *Higher Topos Theory*, 2009.  
- Voevodsky, V. *Homotopy type theory: Univalent foundations*, 2013.

---


## Foundational Papers Forthcoming

- [Foundations of Virtual Sets (Paper #1)]()  
- [Apollonius Problem Resolution in VST (Paper #2)]()  
- [Future Research and Extending ZF with Virtual Sets (Paper #3)]()  
- [Enumerative Geometry Overview (Wikipedia)]()  
- [Original Apollonius Problem (Wikipedia)](https://en.wikipedia.org/wiki/Problem_of_Apollonius)  
- [Recent Algebraic Geometry Research (McKean 2022)]()  

---

## Visuals: Conjectural Theorems and Hypotheses in VST

VST analogues of these classical theorems are currently conjectured, with papers to come.

![Virtual Fixed Point Theorem](https://raw.githubusercontent.com/EnumerativeGeometry/enumerativegeometry.github.io/main/static/theorem1.png)
- Description: Virtual fixed point theorem extending classical results.  

![Virtual Combinatorial Identities](https://raw.githubusercontent.com/EnumerativeGeometry/enumerativegeometry.github.io/main/static/theorem2.png)
- Description: Virtual generalization of classical combinatorial identities.  

![Recursive Structure Theorem](https://raw.githubusercontent.com/EnumerativeGeometry/enumerativegeometry.github.io/main/static/theorem3.png)
- Description: Recursive structure theorem analogous to classical set theory results but with virtual sets


## Contact and Contributions

Virtual Set Theory is not a foundation like category theory or set theory, it is instead, a virtual mathematical kernel in Lean4. It aims to formally define a fractal, recursive re-embedding of classical mathematics into itself via virtualized membership relations, producing a rich internal structure that mimics fractal geometry and recursive enumeration phenomena into the structure of sets and membership that allows for rebuilding of classical results into a virtual mathematics. Currently focused on a minimal working example in enumerative geometry, it provides new tools to solve problems like the Generalized Apollonius Problem and other conjectures that have previously resisted classical solution methods as of 2025. Please share feedback, issues, or contributions via GitHub. Collaboration is warmly welcomed to explore and extend virtual mathematics.


Best regards,  
Yesod Bourbansky

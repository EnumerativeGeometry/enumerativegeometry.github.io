/-
  Definitions for Virtual Set Theory and Moduli Space
  ---------------------------------------------------

  This file defines key objects such as the moduli space M
  parameterizing points, lines, circles using triples (x,y,r).
-/

-- Using real numbers from mathlib (import real numbers)
import Mathlib.Data.Real.Basic

-- The projective line over ℝ: ℝ extended with infinity
inductive P1Real
| ofReal : ℝ → P1Real
| infinity : P1Real

open P1Real

-- Geometric element: triple (x,y,r)
structure GeometricElement :=
(x : ℝ)
(y : ℝ)
(r : P1Real)

-- Moduli space M defined as the type of these triples
def ModuliSpace := GeometricElement

-- Classification predicates
def is_point (e : ModuliSpace) : Prop := e.r = P1Real.ofReal 0
def is_circle (e : ModuliSpace) : Prop :=
  match e.r with
  | P1Real.ofReal v => v > 0
  | P1Real.infinity => false
  end
def is_line (e : ModuliSpace) : Prop := e.r = P1Real.infinity

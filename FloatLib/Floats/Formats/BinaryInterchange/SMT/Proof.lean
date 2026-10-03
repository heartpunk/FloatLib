/- Refinement facts for the five-mode SMT extension. -/
module
public import FloatLib.Floats.Formats.BinaryInterchange.SMT.Rounding
@[expose] public section
namespace FloatLib.Floats.Formats.BinaryInterchange.Model.SMT
open FloatLib.Numerics

/-- RNA quotient rounding chooses the adjacent integer with least distance;
exact half-way cases always choose the larger magnitude. -/
theorem roundQuot_rna (sign : Bool) (entropy num den : Nat) (hden : den ≠ 0) :
    Policy.roundQuot .nearestAway sign entropy num den =
      if 2 * (num % den) < den then num / den else num / den + 1 := by
  by_cases hzero : num % den = 0
  · simp [Policy.roundQuot, hzero, Nat.pos_of_ne_zero hden]
  · simp [Policy.roundQuot, hzero]


/-- The halfway boundary selects away from zero for both operand signs. -/
theorem roundQuot_rna_tie (sign : Bool) (entropy num den : Nat)
    (hden : den ≠ 0) (htie : 2 * (num % den) = den) :
    Policy.roundQuot .nearestAway sign entropy num den = num / den + 1 := by
  rw [roundQuot_rna sign entropy num den hden]
  simp [htie]

/-- The selected adjacent integer is nearest; strict ties select the upper
magnitude. This is the arithmetic condition applied at every discarded-bit
boundary of the RNA quantization kernel. -/
theorem roundQuot_rna_adjacent (sign : Bool) (entropy num den : Nat) (hden : den ≠ 0) :
    let q := num / den
    let r := num % den
    let result := Policy.roundQuot .nearestAway sign entropy num den
    (result = q ∧ r < den - r) ∨ (result = q + 1 ∧ den - r ≤ r) := by
  dsimp
  rw [roundQuot_rna sign entropy num den hden]
  have hr := Nat.mod_lt num (Nat.pos_of_ne_zero hden)
  split <;> omega

/-- RNA is independent of a stochastic entropy argument. -/
theorem roundQuot_rna_entropy (sign : Bool) (entropy num den : Nat) :
    Policy.roundQuot .nearestAway sign entropy num den =
      Policy.roundQuot .nearestAway sign 0 num den := rfl

/-- The new mode maps to the upstream ties-away quantization kernel, not RNE. -/
theorem roundRNA_eq_policy (fmt : FloatFormat) (value : Numerics.Dyadic) :
    roundRNA fmt value = Policy.roundDyadic fmt
      { rounding := .nearestAway, overflow := .native, underflow := .gradual } 0 value := rfl

/-- Every existing four-mode operation keeps its exact implementation. -/
theorem add_eq_legacy {fmt : FloatFormat} (mode : RoundingMode) (ieee : IEEERoundingMode)
    (h : mode.ieee? = some ieee) (x y : Model fmt) :
    add mode x y = addWithRounding ieee x y := by simp [add, h]
theorem mul_eq_legacy {fmt : FloatFormat} (mode : RoundingMode) (ieee : IEEERoundingMode)
    (h : mode.ieee? = some ieee) (x y : Model fmt) :
    mul mode x y = mulWithRounding ieee x y := by simp [mul, h]
theorem div_eq_legacy {fmt : FloatFormat} (mode : RoundingMode) (ieee : IEEERoundingMode)
    (h : mode.ieee? = some ieee) (x y : Model fmt) :
    div mode x y = divWithRounding ieee x y := by simp [div, h]
theorem fma_eq_legacy {fmt : FloatFormat} (mode : RoundingMode) (ieee : IEEERoundingMode)
    (h : mode.ieee? = some ieee) (x y z : Model fmt) :
    fma mode x y z = fmaWithRounding ieee x y z := by simp [fma, h]
theorem sqrt_eq_legacy {fmt : FloatFormat} (mode : RoundingMode) (ieee : IEEERoundingMode)
    (h : mode.ieee? = some ieee) (hIEEE : fmt.encoding = .ieee) (x : Model fmt) :
    sqrt hIEEE mode x = sqrtWithRounding ieee x := by simp [sqrt, h]

end FloatLib.Floats.Formats.BinaryInterchange.Model.SMT

# Manuscript-to-Lean theorem map

This table prevents an abstract Lean proof from being mistaken for a complete
verification of the number theory.

| Manuscript item | Lean declaration | Status |
|---|---|---|
| `U₂F = 0` characterizes odd support | `oddSupported_iff_U2_eq_zero` | Formalized at coefficient-sequence level |
| Odd support is anti-invariance under `τ ↦ τ + 1/2` | `oddSupported_iff_halfTranslate_eq_neg` | Formalized at coefficient-sequence level |
| Matching first `s` odd coefficients | `oddJetVanishes_sub_iff` | Formalized at coefficient-sequence level |
| Unitriangular coordinates recover the first coordinates | `coords_zero_of_lowerTransform_zero_prefix` | Abstract algebraic core formalized |
| Integral observations force integral rational coordinates | `integral_coords_of_integral_lowerTransform_prefix` | Abstract saturation mechanism formalized |
| Unimodularity preserves common divisibility | `dvd_lowerTransform_prefix_iff` | Abstract arithmetic core formalized |
| Fourier content equals residual-coordinate content | `global_dvd_iff_coordinate_dvd` | Formalized as equality of all common divisors; modular-form instance pending |
| Integral basis theorem, Theorem 4.1 | `OddJetBasisData` interface plus saturation theorem | Not instantiated for `B,C,D` |
| Exact `D²ˢ` factor in the jet filtration | no complete declaration yet | Requires formal `PowerSeries` multiplication and the `B,C,D` basis |
| Ring presentation `M_even = ℚ[B,D]` | target recorded in `Gamma0FourFormalizationTargets` | Not formalized |
| Principal cusp ideal `S_even = C·M_even` | target recorded | Not formalized |
| Eta identities and cusp orders | target recorded | Not formalized |
| Hecke matrices and six exact congruences | target recorded | Not formalized |

## Meaning of “formalized at coefficient-sequence level”

The theorem has been translated into Lean for arbitrary integer coefficient
functions. This validates the logical coefficient manipulation, but it does not
prove that the analytic modular forms in the paper have those coefficients or
that they satisfy the asserted modularity, ring, divisor, or Hecke properties.

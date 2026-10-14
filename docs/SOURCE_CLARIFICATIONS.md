# Source model notes

These notes explain definitions used by the current theory results.

## Theorem 5: distance to the exact prediction fiber

For a fitted parameter Θ⋆, its exact prediction fiber is the set of all Θ
with p(Θ) = p(Θ⋆). Theorem 5 measures distance to this set. For a bilinear
prediction, the one-dimensional factors (u, v) = (1, 1) and (2, 1/2) give the
same prediction. Measuring distance to the entire fiber respects this
invariance. Assumption 1 bounds the Jacobian on directions orthogonal to its
kernel and gives the local Cε/√h distance bound.

## Theorem 3: conditional null probabilities

For a fixed item and fitted item/model factors, the null responses across
models have a product-Bernoulli law. Subtracting those conditional success
probabilities gives zero pair-residual cross moment under the null. Theorem 3
transfers that fact to the true law through the stated discrepancy control.
It does not require independence across items.

Conditioning is material to the definition: if X = Y = B for a Bernoulli(1/2)
latent variable B, then E[(X − 1/2)(Y − 1/2)] = 1/4, whereas both residuals
conditional on B are zero. This example explains the conditional probability
in the null definition.

## Proposition 7: calibration and demeaning

Write ξᵢⱼ = Yᵢⱼ − pⱼ and δᵢⱼ = pⱼ − p̂ᵢⱼ. The raw residual is
ξᵢⱼ + δᵢⱼ, and its centered version is
(ξᵢⱼ − ξ̄ⱼ) + (δᵢⱼ − δ̄ⱼ). Thus demeaning removes average calibration
error and leaves the itemwise centered remainder. The sample mean residual
minus average calibration error equals the sample mean of ξ; the IID law of
large numbers gives the stated convergence even when the fitted probabilities
depend on the whole sample. Remark 1 separately supplies the consistency and
moment-law conditions for empirical covariance and correlation limits.

use ark_poly::{univariate::DensePolynomial, multivariate::{SparsePolynomial, SparseTerm, Term}, DenseMVPolynomial, DenseUVPolynomial};
use ark_std::cfg_into_iter;
use ark_test_curves::fp128::Fq as F;
use ark_test_curves::Zero;
use rand::{Rng, SeedableRng};
use rand::rngs::OsRng;
use ark_poly::Polynomial;
use ark_test_curves::Field;

struct Transcript {
    pub randomness: Vec<F>
}

struct Prover {
    pub polynomial_to_prove: SparsePolynomial<F, SparseTerm>
}

struct Verifier {
    pub last_polynomial: Option<DensePolynomial<F>>,
    pub claimed_value: Option<F>
}

impl Transcript {
    fn new() -> Self {
        Transcript {
            randomness: vec![],
        }
    }
}

impl Verifier {
    fn new() -> Self {
        Verifier {
            last_polynomial: None,
            claimed_value: None,
        }
    }

    fn run_init_round<R: Rng>(&mut self, _transcript: &mut Transcript, _rng: &mut R, claimed_value: F) {
        self.claimed_value = Some(claimed_value);
    }

    fn run_round<R: Rng>(&mut self, transcript: &mut Transcript, polynomial: DensePolynomial<F>, round: usize, rng: &mut R) {
        if round == 0 {
            assert!(self.last_polynomial.is_none());
            let eval = polynomial.evaluate(&0.into()) + polynomial.evaluate(&1.into());
            assert_eq!(eval, self.claimed_value.unwrap());
        } else {
            let last_polynomial = self.last_polynomial.clone().unwrap();
            let eval_1 = last_polynomial.evaluate(&transcript.randomness[round - 1]);
            let eval_2 = polynomial.evaluate(&0.into()) + polynomial.evaluate(&1.into());
            assert_eq!(eval_1, eval_2);
        }
        self.last_polynomial = Some(polynomial);
        transcript.randomness.push(rng.gen());
    }

    fn run_last_round(&mut self, transcript: &mut Transcript, polynomial: SparsePolynomial<F, SparseTerm>) {
        let rand = transcript.randomness[transcript.randomness.len() - 1];
        assert_eq!(polynomial.evaluate(&transcript.randomness), self.last_polynomial.clone().unwrap().evaluate(&rand));
    }
}

impl Prover {
    fn new_random<R: Rng>(rng: &mut R, num_vars: usize) -> Self {
        let mut rng = OsRng::default();
        let polynomial_to_prove = SparsePolynomial::rand(1, num_vars, &mut rng);
        Prover {
            polynomial_to_prove
        }
    }

    // Run the initialization round and return the claimed sum check value
    fn run_init_round(&self, _transcript: &mut Transcript) -> F {
        // Evaluate the polynomial at all possible points
        let mut accum = F::zero();
        for i in 0..2i32.pow(self.polynomial_to_prove.num_vars as u32) {
            let mut counter = i;
            let mut coeffs = vec![];
            for _ in 0..self.polynomial_to_prove.num_vars {
                if counter % 2 == 0 {
                    coeffs.push(0.into());
                } else {
                    coeffs.push(1.into());
                }
                counter /= 2;
            }
            accum += self.polynomial_to_prove.evaluate(&coeffs);
        }
        return accum;
    }

    // Run a round and output polynomials
    fn run_round(&self, round: usize, transcript: &Transcript) -> DensePolynomial<F> {
        assert!(transcript.randomness.len() <= round, "round has not progressed");
        // evaluate at all possible points
        // At round 0, we evaluate everything but one.
        let k = round;
        let to_sum = self.polynomial_to_prove.num_vars - k - 1;

        let mut single_coeffs = vec![F::zero(); self.polynomial_to_prove.degree() + 1];

        for i in 0..2i32.pow(to_sum as u32) {
            // Generate input for current evaluation
            let mut inputs = vec![];
            inputs.extend(transcript.randomness.clone());
            inputs.push(F::zero());
            let mut counter = i;
            for _ in 0..to_sum {
                if counter % 2 == 0 {
                    inputs.push(0.into());
                } else {
                    inputs.push(1.into());
                }
                counter /= 2;
            }

            // Contribute to polynomial
            for (coeff, term) in cfg_into_iter!(&self.polynomial_to_prove.terms) {
                // get degree of X
                let mut coeff_accum: F = 1.into();
                let mut which = 0;
                for (&var, pow) in term.vars().iter().zip(term.powers()) {
                    if var == round {
                        which = pow;
                    } else {
                        coeff_accum *= inputs[var].pow(&[pow as u64]);
                    }
                }
                single_coeffs[which] += coeff * &coeff_accum;
            }
        }
        DensePolynomial::from_coefficients_vec(single_coeffs)
    }
}

fn main() {
    let mut rng = OsRng::default();

    let num_vars = 10;

    let prover = Prover::new_random(&mut rng, num_vars);
    let mut verifier = Verifier::new();
    let mut transcript = Transcript::new();

    let claimed_value = prover.run_init_round(&mut transcript);
    verifier.run_init_round(&mut transcript, &mut rng, claimed_value);

    for round in 0..num_vars {
        let polynomial = prover.run_round(round, &mut transcript);
        verifier.run_round(&mut transcript, polynomial, round, &mut rng);
    }

    // let claimed_eval = prover.run_last_round(&mut transcript);
    verifier.run_last_round(&mut transcript, prover.polynomial_to_prove);
}

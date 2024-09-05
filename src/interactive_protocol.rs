#[derive(PartialEq, Debug)]
pub enum VerifierResponse<Challange> {
    Challenge(Challange),
    Failed(String),
    Success,
}

pub trait InteractiveProver<ProverResponse, Challenge> {
    fn start(&mut self) -> ProverResponse;
    fn next(&mut self, ch: Challenge) -> ProverResponse;
}

pub trait InteractiveVerifier<ProverResponse, Challenge> {
    fn verify(&mut self, p: ProverResponse) -> VerifierResponse<Challenge>;
}

#[must_use]
pub fn test_interactive_protocol<PR, CH, P, V>(prover: &mut P, verifier: &mut V) -> Result<(),String>
where
    P: InteractiveProver<PR, CH>,
    V: InteractiveVerifier<PR, CH>,
{
    let mut prover_response = prover.start();
    loop {
        match verifier.verify(prover_response) {
            VerifierResponse::Challenge(ch) => {
                prover_response = prover.next(ch);
            }
            VerifierResponse::Failed(err) => return Err(err),
            VerifierResponse::Success => return Ok(()) 
        }
    }
}

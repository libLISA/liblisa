use liblisa::arch::Arch;
use liblisa::oracle::Oracle;

pub trait Work<A: Arch, C: Send + Sync> {
    type RuntimeData;
    type Request;
    type Result;
    type Artifact;

    fn next(&mut self, data: &mut Self::RuntimeData) -> Option<Self::Request>;
    fn complete(&mut self, data: &mut Self::RuntimeData, request: Self::Request, result: Self::Result) -> Option<Self::Artifact>;

    fn run<O: Oracle<A>>(oracle: &mut O, cache: &C, request: &Self::Request) -> Self::Result;
}

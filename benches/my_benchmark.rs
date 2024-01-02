use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ecdsa::run_ecdsa_threshold;
use threshold_ecdsa::{
    ecdsa::{self, run_ecdsa_benchmarking, run_ecdsa},
    groups,
    nat::Nat,
    schnorr::{self, run_schnorr_threshold},
};

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("Run threshold ecdsa", |b| {
        b.iter(|| run_ecdsa_threshold(black_box(Nat::from_u16(1337))))
    });

    c.bench_function("Run non-threshold ecdsa", |b| {
        b.iter(|| run_ecdsa(black_box(Nat::from_u16(1337))))
    });

    c.bench_function("Run benchmarking crypto ecdsa", |b| {
        b.iter(|| run_ecdsa_benchmarking(black_box(Nat::from_u16(1337))))
    });

    let group = groups::GroupSpec::new();
    let (g_r1, g_r2, r1, r2) = schnorr::preprocess_mod(&group);
    c.bench_function("Run schnorr without random preprocessing", |b| {
        b.iter(move || {
            run_schnorr_threshold(
                black_box(Nat::from_u16(1337)),
                false,
                g_r1,
                g_r2,
                r1,
                r2,
                groups::GroupSpec {
                    p: group.p,
                    q: group.q,
                    alpha: group.alpha,
                },
            )
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ecdsa::run_ecdsa_bedoza;
use threshold_ecdsa::{
    ecdsa::{self, run_ecdsa_plain},
    groups,
    nat::Nat,
    schnorr::{self, run_schnorr},
};

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("Run BeDOZa ecdsa", |b| {
        b.iter(|| run_ecdsa_bedoza(black_box(Nat::from_u16(1337))))
    });

    c.bench_function("Run plain ecdsa", |b| {
        b.iter(|| run_ecdsa_plain(black_box(Nat::from_u16(1337))))
    });

    let group = groups::GroupSpec::new();
    let (g_r1, g_r2, r1, r2) = schnorr::preprocess_mod(&group);
    c.bench_function("Run schnorr without random preprocessing", |b| {
        b.iter(move || {
            run_schnorr(
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

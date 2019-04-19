use criterion::*;
use halfbrown;
use hashbrown;
use std::collections;

const NAMES: [&'static str; 162] = [
    // Some data taken from the twitter json
    "contributors",
    "coordinates",
    "created_at",
    "entities",
    "favorite_count",
    "favorited",
    "geo",
    "id",
    "id_str",
    "in_reply_to_screen_name",
    "in_reply_to_status_id",
    "in_reply_to_status_id_str",
    "in_reply_to_user_id",
    "in_reply_to_user_id_str",
    "lang",
    "metadata",
    "place",
    "possibly_sensitive",
    "retweet_count",
    "retweeted",
    "retweeted_status",
    "source",
    "text",
    "truncated",
    "user",
    "completed_in",
    "count",
    "max_id",
    "max_id_str",
    "next_results",
    "query",
    "refresh_url",
    "since_id",
    "since_id_str",
    // Some random names
    "Molly",
    "Queenie",
    "Fredrick",
    "Elwanda",
    "Philip",
    "Idella",
    "Cinderella",
    "Edith",
    "Halina",
    "Marchelle",
    "Era",
    "Louann",
    "Sheryll",
    "Arlinda",
    "Keira",
    "Nickie",
    "Shondra",
    "Andy",
    "Kelli",
    "Crissy",
    "Sherita",
    "Samara",
    "Brock",
    "Bridget",
    "Mauricio",
    "Marcus",
    "data",
    "name",
    "rows",
    "rows_per_beat",
    "rows_per_measure",
    "Jeannetta",
    "Vickey",
    "Marco",
    "Branda",
    "Patricia",
    "Alexis",
    "Yoko",
    "Milford",
    "Sandra",
    "Cherie",
    "contributors_enabled",
    "created_at",
    "default_profile",
    "default_profile_image",
    "description",
    "entities",
    "favourites_count",
    "follow_request_sent",
    "followers_count",
    "following",
    "friends_count",
    "geo_enabled",
    "id",
    "id_str",
    "is_translation_enabled",
    "is_translator",
    "lang",
    "listed_count",
    "location",
    "name",
    "notifications",
    "profile_background_color",
    "profile_background_image_url",
    "profile_background_image_url_https",
    "profile_background_tile",
    "profile_banner_url",
    "profile_image_url",
    "profile_image_url_https",
    "profile_link_color",
    "profile_sidebar_border_color",
    "profile_sidebar_fill_color",
    "profile_text_color",
    "profile_use_background_image",
    "protected",
    "screen_name",
    "statuses_count",
    "time_zone",
    "url",
    "utc_offset",
    "verified",
    "Dulcie",
    "Nancey",
    "Johnson",
    "Sibyl",
    "Janice",
    "Stevie",
    "Reatha",
    "Norbert",
    "Jessi",
    "Kristen",
    "Tarah",
    "Narcisa",
    "Iva",
    "Aleen",
    "default_filter_cutoff",
    "default_filter_cutoff_enabled",
    "default_filter_mode",
    "default_filter_resonance",
    "default_filter_resonance_enabled",
    "default_pan",
    "duplicate_check_type",
    "duplicate_note_action",
    "fadeout",
    "global_volume",
    "graph_insert",
    "legacy_filename",
    "midi_bank",
    "midi_channel",
    "midi_drum_set",
    "midi_program",
    "name",
    "new_note_action",
    "note_map",
    "panning_envelope",
    "pitch_envelope",
    "pitch_pan_center",
    "pitch_pan_separation",
    "pitch_to_tempo_lock",
    "random_cutoff_weight",
    "random_pan_weight",
    "random_resonance_weight",
    "random_volume_weight",
    "sample_map",
    "tuning",
    "volume_envelope",
    "volume_ramp_down",
    "volume_ramp_up",
];

fn bench(cnt: usize, cap: usize) -> ParameterizedBenchmark<std::vec::Vec<&'static str>>{
    let data1: Vec<&'static str> = NAMES.iter().cloned().take(cnt).collect();

    ParameterizedBenchmark::new(
        "halfbrown",
        move |b, data| {
            b.iter_batched(
                || data.clone(),
                |data| {
                    let mut m = halfbrown::HashMap::with_capacity(cap);
                    for e in data {
                        m.insert(e, e);
                    }
                },
                BatchSize::SmallInput,
            )
        },
        vec![data1],
    )
        .with_function("halfbrown(nocheck)", move |b, data| {
            b.iter_batched(
                || data.clone(),
                |data| {
                    let mut m = halfbrown::HashMap::with_capacity(cap);
                    for e in data {
                        m.insert_nocheck(e, e);
                    }
                },
                BatchSize::SmallInput,
            )
        })    .with_function("hashbrown", move |b, data| {
        b.iter_batched(
            || data.clone(),
            |data| {
                let mut m = hashbrown::HashMap::with_capacity(cap);
                for e in data {
                    m.insert(e, e);
                }
            },
            BatchSize::SmallInput,
        )
    })
    .with_function("std", move |b, data| {
        b.iter_batched(
            || data.clone(),
            |data| {
                let mut m = collections::HashMap::with_capacity(cap);
                for e in data {
                    m.insert(e, e);
                }
            },
            BatchSize::SmallInput,
        )
    })
}

fn insert_5_capacity(c: &mut Criterion) {
    c.bench("insert(5) with capacity", bench(5, 5));
}

fn insert_9_capacity(c: &mut Criterion) {
    c.bench("insert(9) with capacity", bench(9, 9));
}

fn insert_17_capacity(c: &mut Criterion) {
    c.bench("insert(17) with capacity", bench(17, 17));
}

fn insert_33_capacity(c: &mut Criterion) {
    c.bench("insert(33) with capacity", bench(33, 33));
}

fn insert_49_capacity(c: &mut Criterion) {
    c.bench("insert(49) with capacity", bench(49, 49));
}

fn insert_65_capacity(c: &mut Criterion) {
    c.bench("insert(65) with capacity", bench(65, 65));
}

fn insert_129_capacity(c: &mut Criterion) {
    c.bench("insert(129) with capacity", bench(129, 128));
}


criterion_group!(capacity, insert_5_capacity, insert_9_capacity, insert_17_capacity, insert_33_capacity, insert_49_capacity, insert_65_capacity, insert_129_capacity);

fn insert_5(c: &mut Criterion) {
    c.bench("insert(5)", bench(5, 0));
}

fn insert_9(c: &mut Criterion) {
    c.bench("insert(9)", bench(9, 0));
}

fn insert_17(c: &mut Criterion) {
    c.bench("insert(17)", bench(17, 0));
}

fn insert_33(c: &mut Criterion) {
    c.bench("insert(33)", bench(33, 0));
}

fn insert_49(c: &mut Criterion) {
    c.bench("insert(49)", bench(49, 0));
}

fn insert_65(c: &mut Criterion) {
    c.bench("insert(65)", bench(65, 0));
}

fn insert_129(c: &mut Criterion) {
    c.bench("insert(129)", bench(129, 0));
}

criterion_group!(alloc, insert_5, insert_9, insert_17, insert_33, insert_49, insert_65, insert_129);

criterion_main!(capacity, alloc);

/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Code to get timing data for the FSE submission.

use cedar_policy::{cedar_test_impl::*, integration_testing::*};

use cedar_drt::ast::{PolicySet, Request};
use cedar_drt::{Entities, JavaDefinitionalEngine, LeanDefinitionalEngine};
use std::{collections::HashMap, io::Write, path::Path};
use walkdir::WalkDir;

const NUM_TRIALS: u32 = 10;

/// Parse a file in the integration test format, ignoring the schema and
/// expected authorization/validation results.
fn parse_test(jsonfile: impl AsRef<Path>) -> (PolicySet, Entities, Vec<Request>) {
    let jsonfile = resolve_integration_test_path(jsonfile);
    let test_name: String = jsonfile.display().to_string();
    let jsonstr = std::fs::read_to_string(jsonfile.as_path())
        .unwrap_or_else(|e| panic!("error reading from file {test_name}: {e}"));
    let test: JsonTest =
        serde_json::from_str(&jsonstr).unwrap_or_else(|e| panic!("error parsing {test_name}: {e}"));

    let policies = parse_policies_from_test(&test);
    let schema = parse_schema_from_test(&test);
    let entities = parse_entities_from_test(&test, &schema);
    let requests = test
        .requests
        .iter()
        .map(|json_request| parse_request_from_test(&json_request, &schema, &test_name))
        .collect();

    (policies, entities, requests)
}

/// Run every input in the directory through the provided Cedar test
/// implementation and return timing info. The output maps a type of
/// timing (e.g., "total") to a map of tests to trial results.
fn run_timing_tests(
    folder: impl AsRef<Path>,
    custom_impl: &dyn CedarTestImplementation,
) -> HashMap<&str, HashMap<String, Vec<u128>>> {
    let folder = resolve_integration_test_path(folder);
    let tests = WalkDir::new(&folder)
        .into_iter()
        .map(|e| e.expect("failed to access file").into_path())
        .filter(|p| {
            let filename = p
                .file_name()
                .expect("didn't expect subdirectories")
                .to_str()
                .expect("expected filenames to be valid UTF-8");
            filename.ends_with(".json")
                && !filename.ends_with(".cedarschema.json")
                && !filename.ends_with(".entities.json")
        });
    let mut results = HashMap::new();
    results.insert("total", HashMap::new());
    results.insert("authorize", HashMap::new());
    results.insert("authorize_and_parse", HashMap::new());
    for test in tests {
        let test_name = String::from(test.file_name().unwrap().to_str().unwrap());
        println!("Running test: {:?}", test_name);
        let (policies, entities, requests) = parse_test(test);
        let mut i = 0;
        for request in requests {
            let mut total_results = Vec::new();
            let mut auth_results = Vec::new();
            let mut auth_and_parse_results = Vec::new();
            for _j in 0..NUM_TRIALS {
                let (response, duration) =
                    time_function(|| custom_impl.is_authorized(&request, &policies, &entities));
                let response = response.expect("Unexpected test failure");
                total_results.push(duration.as_micros());
                if response.timing_info.contains_key("authorize") {
                    auth_results.push(response.timing_info["authorize"]);
                }
                if response.timing_info.contains_key("authorize_and_parse") {
                    auth_and_parse_results.push(response.timing_info["authorize_and_parse"]);
                }
            }
            results
                .get_mut("total")
                .unwrap()
                .insert(format!("{test_name}_request{i}"), total_results);
            results
                .get_mut("authorize")
                .unwrap()
                .insert(format!("{test_name}_request{i}"), auth_results);
            results
                .get_mut("authorize_and_parse")
                .unwrap()
                .insert(format!("{test_name}_request{i}"), auth_and_parse_results);
            i += 1;
        }
    }
    results
}

/// Write the returned timing info to the specified file in csv format.
fn write_results(filename: impl AsRef<Path>, timing_data: &HashMap<String, Vec<u128>>) {
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&filename)
        .expect("Failed to open file");

    for (test, trials) in timing_data {
        let trials_string = trials
            .iter()
            .map(|x| x.to_string() + ",")
            .collect::<String>();
        let trials_string = trials_string.trim_end_matches(",");
        file.write(format!("{test},{trials_string}\n").as_bytes())
            .unwrap();
    }
}

#[test]
fn run_all_tests() {
    // Create authorization engines
    let rust_impl = RustEngine::new();
    let lean_def_impl = LeanDefinitionalEngine::new();
    let java_def_impl =
        JavaDefinitionalEngine::new().expect("failed to create Dafny definitional engine");

    // Run on abac-lean-corpus
    let timing_data = run_timing_tests(Path::new("abac-lean-corpus"), &rust_impl);
    write_results("rust_auth.csv", timing_data.get("authorize").unwrap());
    write_results("rust_total.csv", timing_data.get("total").unwrap());

    let timing_data = run_timing_tests(Path::new("abac-lean-corpus"), &lean_def_impl);
    write_results("lean_auth.csv", timing_data.get("authorize").unwrap());
    write_results("lean_total.csv", timing_data.get("total").unwrap());

    let timing_data = run_timing_tests(Path::new("abac-lean-corpus"), &java_def_impl);
    write_results(
        "dafny_auth_parse.csv",
        timing_data.get("authorize_and_parse").unwrap(),
    );
    write_results("dafny_total.csv", timing_data.get("total").unwrap());

    // Run on abac-type-directed-lean-corpus
    let timing_data = run_timing_tests(Path::new("abac-type-directed-lean-corpus"), &rust_impl);
    write_results(
        "rust_auth_type_directed.csv",
        timing_data.get("authorize").unwrap(),
    );
    write_results(
        "rust_total_type_directed.csv",
        timing_data.get("total").unwrap(),
    );

    let timing_data = run_timing_tests(Path::new("abac-type-directed-lean-corpus"), &lean_def_impl);
    write_results(
        "lean_auth_type_directed.csv",
        timing_data.get("authorize").unwrap(),
    );
    write_results(
        "lean_total_type_directed.csv",
        timing_data.get("total").unwrap(),
    );

    let timing_data = run_timing_tests(Path::new("abac-type-directed-lean-corpus"), &java_def_impl);
    write_results(
        "dafny_auth_parse_type_directed.csv",
        timing_data.get("authorize_and_parse").unwrap(),
    );
    write_results(
        "dafny_total_type_directed.csv",
        timing_data.get("total").unwrap(),
    );
}

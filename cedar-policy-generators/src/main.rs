use std::{fs::File, io};

use anyhow::{anyhow, Result};
use arbitrary::Unstructured;
use cedar_policy_core::{
    ast::{Expr, PolicyID, PolicySet},
    entities::{Entities, TCComputation},
};
use cedar_policy_generators::{
    abac::Type, hierarchy::{
        EntityUIDGenMode, Hierarchy, HierarchyGenerator, HierarchyGeneratorMode, NumEntities,
    }, policy::GeneratedPolicy, schema::Schema, settings::ABACSettings
};
use cedar_policy_validator::SchemaFragment;
use clap::{Args, Parser, Subcommand};
use rand::{thread_rng, Rng};

#[derive(Parser, Debug)]
struct Cli {
    /// Random byte length
    #[arg(short, long, default_value_t = 4096)]
    byte_length: u16,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Generate random hierarchy
    Hierarchy(HierarchyArgs),
}

#[derive(Args, Debug)]
pub struct HierarchyArgs {
    /// Schema file
    #[arg(short, long = "schema", value_name = "FILE")]
    pub schema_file: String,
    /// Exact number of entities to generate
    /// (if this is omitted, then you will get 1 to max_depth per entity type)
    #[arg(long)]
    pub num_entities: Option<usize>,
    /// Maximum depth
    #[arg(long, default_value_t = 4)]
    pub max_depth: usize,
    /// Maximum width
    #[arg(long, default_value_t = 4)]
    pub max_width: usize,
    #[arg(long, default_value_t = EntityUIDGenMode::default_nanoid_len())]
    pub uid_length: usize,
}

impl From<&HierarchyArgs> for ABACSettings {
    fn from(value: &HierarchyArgs) -> Self {
        Self {
            match_types: true,
            enable_extensions: true,
            max_depth: value.max_depth,
            max_width: value.max_width,
            enable_additional_attributes: false,
            enable_like: true,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: false,
            enable_unknowns: false,
            enable_unspecified_apply_spec: true,
            enable_action_in_constraints: true,
        }
    }
}

fn generate_hierarchy_from_schema(byte_length: usize, args: &HierarchyArgs) -> Result<Entities> {
    let f = File::open(&args.schema_file)?;
    let fragment = SchemaFragment::from_file(f)?;
    let mut rng = thread_rng();
    let mut bytes = Vec::with_capacity(byte_length);
    bytes.resize_with(byte_length, || rng.gen());
    let mut u = Unstructured::new(&bytes);
    let schema = Schema::from_schemafrag(fragment, args.into(), &mut u)
        .map_err(|err| anyhow!("failed to construct `Schema`: {err:#?}"))?;
    let h = HierarchyGenerator {
        mode: HierarchyGeneratorMode::SchemaBased { schema: &schema },
        uid_gen_mode: EntityUIDGenMode::Nanoid(args.uid_length),
        num_entities: match args.num_entities {
            Some(exact_num) => NumEntities::Exactly(exact_num),
            None => NumEntities::RangePerEntityType(1..=args.max_depth),
        },
        u: &mut u,
    }
    .generate()
    .map_err(|err| anyhow!("failed to generate hierarchy: {err:#?}"))?;
    // this is just to ensure no cycles.
    // we throw away the `Entities` built with `ComputeNow`, because we want to
    // generate hierarchies that aren't necessarily TC-closed.
    Entities::from_entities(h.entities().cloned(), TCComputation::ComputeNow)?;
    Ok(Entities::from_entities(
        h.entities().cloned(),
        // use `AssumeAlreadyComputed` because we want a hierarchy that isn't
        // necessarily TC-closed.
        TCComputation::AssumeAlreadyComputed,
    )?)
}

fn generate_hierarchy(filename: &str, u: &mut Unstructured<'_>) -> Result<(Hierarchy, Schema)> {
    let f = File::open(filename)?;

    let fragment = SchemaFragment::from_file(f)?;

    let settings = ABACSettings {
        match_types: true,
        enable_extensions: true,
        max_depth: 6,
        max_width: 40,
        enable_additional_attributes: false,
        enable_like: true,
        enable_action_groups_and_attrs: true,
        enable_arbitrary_func_call: false,
        enable_unknowns: false,
        enable_unspecified_apply_spec: true,
        enable_action_in_constraints: true,
    };
    let schema = Schema::from_schemafrag(fragment, settings, u)
        .map_err(|err| anyhow!("failed to construct `Schema`: {err:#?}"))?;
    let h = HierarchyGenerator {
        mode: HierarchyGeneratorMode::SchemaBased { schema: &schema },
        uid_gen_mode: EntityUIDGenMode::Nanoid(6),
        num_entities: NumEntities::Exactly(120),
        u: u,
    }
    .generate()
    .map_err(|err| anyhow!("failed to generate hierarchy: {err:#?}"))?;
    Ok((h, schema))
}

fn generate_expr<'a>(
    schema: &'a Schema,
    hierarchy: &'a Hierarchy,
) -> Result<cedar_policy_core::ast::Expr, cedar_policy_generators::err::Error> {
    let mut rng = thread_rng();
    let mut bytes = Vec::with_capacity(1);
    bytes.resize_with(64, || rng.gen());
    let mut u = Unstructured::new(&bytes);
    let mut expr_generator = schema.exprgenerator(Some(&hierarchy));
    expr_generator.generate_expr_for_type(&Type::Bool, 8, &mut u)
}

fn main() {
    let size: usize = 1000000;
    let mut bytes = Vec::with_capacity(1);
    let mut rng = thread_rng();
    bytes.resize_with(size, || rng.gen());
    let mut u = Unstructured::new(&bytes);

    let (hierarchy, schema) = match generate_hierarchy("workforce.json", &mut u) {
        Ok((h, s)) => (h, s),
        Err(err) => {
            eprintln!("{err}");
            return;
        }
    };

    let entities =
        match Entities::from_entities(hierarchy.entities().cloned(), TCComputation::ComputeNow) {
            Ok(e) => e,
            Err(err) => {
                eprintln!("{err}");
                return;
            }
        };

    println!("ENTITIES");
    entities.write_to_json(io::stdout()).unwrap_or_else(|err| eprintln!("cannot convert entities to JSON: {err}"));

    println!("\n\nPOLICIES:");

    let mut policy_set = PolicySet::new();
    for i in 1..1000 {
        let policy_id = PolicyID::from_string(format!("policy_{i}"));
        let abac_expr = match generate_expr(&schema, &hierarchy) {
            Ok(expr) => expr,
            Err(_) => Expr::val(true),
        };
        let generated_policy = GeneratedPolicy::arbitrary_for_hierarchy(
            Some(policy_id),
            &hierarchy,
            true,
            abac_expr,
            &mut u,
        );
        match generated_policy {
            Ok(gp) => {
                gp.add_to_policyset(&mut policy_set);
            }
            Err(err) => {
                eprintln!("{err}");
                continue;
            }
        }
    }
    use itertools::Itertools;
    println!(
        "@@@TEMPLATES:\n{}\n\n @@@POLICIES:\n{}",
        policy_set.all_templates().map(|t| t.to_string()).join("\n"),
        policy_set.policies().map(|p| p.to_string()).join("\n")
    )
}

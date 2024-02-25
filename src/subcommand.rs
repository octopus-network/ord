use super::*;

pub mod balances;
pub mod decode;
pub mod epochs;
pub mod find;
pub mod index;
pub mod list;
pub mod parse;
pub mod runes;
pub(crate) mod server;
pub mod subsidy;
pub mod supply;
pub mod teleburn;
pub mod traits;
pub mod wallet;

#[derive(Debug, Parser)]
pub(crate) enum Subcommand {
  #[command(about = "List all rune balances")]
  Balances,
  #[command(about = "Decode a transaction")]
  Decode(decode::Decode),
  #[command(about = "List the first satoshis of each reward epoch")]
  Epochs,
  #[command(about = "Find a satoshi's current location")]
  Find(find::Find),
  #[command(subcommand, about = "Index commands")]
  Index(index::IndexSubcommand),
  #[command(about = "List the satoshis in an output")]
  List(list::List),
  #[command(about = "Parse a satoshi from ordinal notation")]
  Parse(parse::Parse),
  #[command(about = "List all runes")]
  Runes,
  #[command(about = "Run the explorer server")]
  Server(server::Server),
  #[command(about = "Display information about a block's subsidy")]
  Subsidy(subsidy::Subsidy),
  #[command(about = "Display Bitcoin supply information")]
  Supply,
  #[command(about = "Generate teleburn addresses")]
  Teleburn(teleburn::Teleburn),
  #[command(about = "Display satoshi traits")]
  Traits(traits::Traits),
  #[command(about = "Wallet commands")]
  Wallet(wallet::WalletCommand),
}

impl Subcommand {
  pub(crate) fn run(self, options: Options) -> SubcommandResult {
    match self {
      Self::Balances => balances::run(options),
      Self::Decode(decode) => decode.run(options),
      Self::Epochs => epochs::run(),
      Self::Find(find) => find.run(options),
      Self::Index(index) => index.run(options),
      Self::List(list) => list.run(options),
      Self::Parse(parse) => parse.run(),
      Self::Runes => runes::run(options),
      Self::Server(server) => {
        let runtime = Arc::new(Runtime::new()?);
        let mut index = Index::open(&options)?;
        if options.index_runes {
          let runtime_clone = Arc::clone(&runtime);
          runtime.block_on(async {
            index
              .init_pg_pool(&runtime_clone)
              .await
              .expect("Failed to initialize PgPool");
          });
          index.set_runtime(runtime_clone);
        }

        let index = Arc::new(index);
        let handle = axum_server::Handle::new();
        LISTENERS.lock().unwrap().push(handle.clone());
        server.run(options, runtime, index, handle)
      }
      Self::Subsidy(subsidy) => subsidy.run(),
      Self::Supply => supply::run(),
      Self::Teleburn(teleburn) => teleburn.run(),
      Self::Traits(traits) => traits.run(),
      Self::Wallet(wallet) => wallet.run(options),
    }
  }
}

pub trait Output: Send {
  fn print_json(&self, minify: bool);
}

impl<T> Output for T
where
  T: Serialize + Send,
{
  fn print_json(&self, minify: bool) {
    if minify {
      serde_json::to_writer(io::stdout(), self).ok();
    } else {
      serde_json::to_writer_pretty(io::stdout(), self).ok();
    }
    println!();
  }
}

pub(crate) type SubcommandResult = Result<Option<Box<dyn Output>>>;

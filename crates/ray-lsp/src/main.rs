use ray_lsp::run_stdio_server;

#[tokio::main]
async fn main() {
    let _ = env_logger::try_init();
    run_stdio_server().await;
}

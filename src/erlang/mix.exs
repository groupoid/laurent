defmodule Laurent.MixProject do
  use Mix.Project

  def project do
    [
      app: :laurent,
      version: "0.3.10",
      description: "The Laurent Programming Language",
      deps: deps(),
      package: package()
    ]
  end

  def application do
    [ extra_applications: [ :logger ] ]
  end

  def deps do
    [
      {:ex_doc, ">= 0.0.0", only: :dev}
    ]
  end

  def package() do
    [
      files: [ "README.md", "LICENSE" ],
      licenses: ["ISC"],
      maintainers: ["Namdak Tonpa"],
      name: :laurent,
      links: %{"GitHub" => "https://github.com/groupoid/laurent"}
    ]
  end

end

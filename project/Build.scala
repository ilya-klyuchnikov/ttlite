import sbt._
import Keys._

object TTLiteBuild extends Build {

  override lazy val settings = super.settings ++ Seq(
    scalaVersion := "2.10.3",
    organization := "ttlite",
    version := "0.5-SNAPSHOT",
    resolvers += "lambdamix-bintray" at "http://dl.bintray.com/lambdamix/maven/",
    libraryDependencies += "org.scalatest" %% "scalatest" % "2.0" % "test,it",
    baseDirectory in run := file("."),
    testOptions in Test += Tests.Argument("-oD"),
    testOptions in IntegrationTest += Tests.Argument("-oD"),
    parallelExecution in Test := false,
    parallelExecution in IntegrationTest := false
  )

  lazy val CoreProject =
    Project("ttlite-core", file("ttlite-core"))
      .configs(IntegrationTest)
      .settings( Defaults.itSettings : _*)
      .settings(
        name := "core",
        libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.5.1",
        libraryDependencies += "org.fusesource.jansi" %  "jansi" % "1.11"
      )

  lazy val ScProject =
    Project("ttlite-sc", file("ttlite-sc"))
      .configs(IntegrationTest)
      .settings( Defaults.itSettings : _*)
      .settings(
        name := "sc",
        libraryDependencies += "mrsc" %% "mrsc" % "0.5")
      .dependsOn(CoreProject)

  lazy val root =
    Project(id = "ttlite", base = file("."))
      .configs(IntegrationTest)
      .settings( Defaults.itSettings : _*)
      .aggregate(CoreProject, ScProject)
}

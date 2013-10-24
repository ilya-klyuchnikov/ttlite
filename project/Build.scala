import sbt._
import Keys._

object TTLiteBuild extends Build {

  override lazy val settings = super.settings ++ Seq(
    scalaVersion := "2.10.3",
    organization := "ttlite",
    version := "0.5-SNAPSHOT",
    resolvers += "lambdamix-bintray" at "http://dl.bintray.com/lambdamix/maven/",
    libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.2" % "test",
    baseDirectory in run := file("."),
    testOptions in Test += Tests.Argument("-oD"),
    parallelExecution in Test := false
  )

  lazy val CoreProject = Project("ttlite-core", file("ttlite-core"),
    settings = Project.defaultSettings ++ Seq(
      name := "core",
      libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.5.1"
    )
  )

  lazy val ScProject = Project("ttlite-sc", file("ttlite-sc"),
    settings = Project.defaultSettings ++ Seq(
      name := "sc",
      libraryDependencies += "mrsc" %% "mrsc" % "0.5"
    )
  ) dependsOn CoreProject

  lazy val root = Project(id = "ttlite", base = file(".")) aggregate(CoreProject, ScProject)
}

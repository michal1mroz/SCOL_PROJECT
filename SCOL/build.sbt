ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.4.0"

lazy val root = (project in file("."))
  .settings(
    name := "SCOL"
  )

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.11" % Test


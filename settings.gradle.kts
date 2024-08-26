/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2023 The While* Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

plugins {
  id("com.gradle.develocity") version "3.17.2"
  id("org.gradle.toolchains.foojay-resolver-convention") version "0.8.0"
}

rootProject.name = "wvm"

develocity {
  buildScan {
    val isCI = System.getenv("CI").isNullOrEmpty().not()
    publishing.onlyIf { isCI }
    if (isCI) {
      tag("CI")
      uploadInBackground = false
      termsOfUseUrl = "https://gradle.com/help/legal-terms-of-use"
      termsOfUseAgree = "yes"
    }
  }
}
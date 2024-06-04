/*
 * Copyright Cedar Contributors
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

//! This module contains the entry point to the wasm isAuthorized functionality.
use cedar_policy::ffi;
use wasm_bindgen::prelude::*;

#[wasm_bindgen(js_name = "isAuthorized")]
pub fn wasm_is_authorized(call: ffi::AuthorizationCall) -> ffi::AuthorizationAnswer {
    ffi::is_authorized(call)
}

import React, { useState } from 'react';

function NavBar() {
    return (
        <header>
            <nav className="navbar border">
                <ul class="nav">
                    <li class="nav-item">
                        <h3>Explainable Ai</h3>
                    </li>
                </ul>
                <span class="navbar-text">
                    <a href="">GitHub</a>
                </span>
            </nav>
        </header>
    )
}

export default NavBar;